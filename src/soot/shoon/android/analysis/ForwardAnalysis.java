package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.IdentityUnit;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.TaintValue;

//forward analysis begins when meet a new taint value 
public class ForwardAnalysis {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private ISourceSinkManager issm;
	private IInfoflowCFG icfg;

	private SinglePathAnalysis spa;
	private Unit activationUnit;
	
	private AliasValue currAliasValue;
	
	//this is used for the first ForwardAnalysis
	public ForwardAnalysis(Unit activationUnit, SinglePathAnalysis spa){
		this.activationUnit = activationUnit;
		this.spa = spa;
		this.issm = AnalysisManager.v().getISSM();
		this.icfg = AnalysisManager.v().getICFG();
		this.currAliasValue = null;
	}
	
	//this is used when found an alias
	public ForwardAnalysis(Unit activationUnit, SinglePathAnalysis spa, AliasValue av){
		this.activationUnit = activationUnit;
		this.spa = spa;
		this.issm = AnalysisManager.v().getISSM();
		this.icfg = AnalysisManager.v().getICFG();
		this.currAliasValue = av;
	}
	
	public void startForward(){
		int currIndex = spa.getPathSummary().indexOfUnit(activationUnit);
		int stopIndex = 0;
		if(currAliasValue == null){
			stopIndex = spa.getPathSummary().getPathLength();
		}else{
			stopIndex = spa.getPathSummary().indexOfUnit(currAliasValue.getSource().getActivation());
			currIndex++;
		}
		while(currIndex < stopIndex){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				Value lv = s.getLeftOp();
				Value rv = s.getRightOp();
			
				//initialize the taints and aliases
				if(this.spa.getMethodAnalysisType() == MethodAnalysisType.Callee){
					TaintValue paramTV = null;
					ArrayList<AliasValue> paramAVs = null;
					//this
					if(rv instanceof ThisRef){
						paramTV = spa.getPathSummary().getInitMethodSummary().getMethodInitState().getThisTV();
						paramAVs = spa.getPathSummary().getInitMethodSummary().getMethodInitState().getThisAVs();
					}else if(rv instanceof ParameterRef){
						ParameterRef pr = (ParameterRef) rv;
						int index = pr.getIndex();
						paramTV = spa.getPathSummary().getInitMethodSummary().getMethodInitState().getArgTaintValue(index);
						paramAVs = spa.getPathSummary().getInitMethodSummary().getMethodInitState().getArgAliasValues(index);
					}
					if(paramTV != null){
						Value tmp = paramTV.getTaintValue();
						if(tmp instanceof InstanceFieldRef){//r0.t = tainted; r0.func();
							InstanceFieldRef ifr = (InstanceFieldRef) tmp;
							AliasValue newAV = new AliasValue(currUnit, null , lv);
							newAV.setActivationIndex(currIndex);
							newAV.appendField(ifr.getFieldRef());
							spa.getPathSummary().addAlias(newAV);
						}else{//r0 = tainted; r0.func
							foundNewTaint(currUnit, lv);
						}
					}
					//r1 = r0; r0.t = tainted; r1.t.func();/r1.func();
					//TODO is the case "r1.t.func()" possible? --> k = r1.t; k.func();
					if(paramAVs != null){
						for(AliasValue paramAV : paramAVs){
							ArrayList<SootFieldRef> accessPath = paramAV.getAccessPath();
							AliasValue newAV = new AliasValue(currUnit, null, lv);
							newAV.setActivationIndex(currIndex);
							for(int i = 0; i < accessPath.size(); i++){
								newAV.appendField(accessPath.get(i));
							}
							spa.getPathSummary().addAlias(newAV);
						}
					}
				}
				
				//if this a source
				AliasValue tmpAV = null;
				TaintValue tmpTV = null;
				if(issm.isSource(s, icfg)){
					foundNewTaint(currUnit, lv);
				}else if(spa.getPathSummary().isTainted(rv, currUnit) != null){//rv is in taintsSet
					foundNewTaint(currUnit, lv);
				}else if(spa.getPathSummary().isAlias(rv, currUnit) != null){
					foundNewTaint(currUnit, lv);
				}else{// the right value is not tainted
					//if the left value is already tainted
					if((tmpTV = spa.getPathSummary().isTainted(lv, currUnit)) != null){
						spa.getPathSummary().deleteTaint(tmpTV);
					}else if((tmpAV = spa.getPathSummary().isAlias(lv, currUnit)) != null){//if the left value is an alias
						spa.getPathSummary().deleteAlias(tmpAV);
					}
					//if the right value is an alias's base, produce a new alias
					//or 
					//p0.f = tainted_value; ——————————— p0.f is tainted
					//p1 = p0; ————————————————- p1.f is an alias ********************bug issue3
					//sink(p1.f); ————————————————  
					if((tmpAV = spa.getPathSummary().isAliasBase(rv, currUnit)) != null){
						Value base = null;
						if(rv instanceof InstanceFieldRef){
							InstanceFieldRef ifr = (InstanceFieldRef) rv;
							base = ifr.getBase();
						}else{
							base = rv;
						}
						AliasValue av = new AliasValue(currUnit, tmpAV.getSource(), base);
						ArrayList<SootFieldRef> accessPath = tmpAV.getAccessPath();
						for(int i = 0; i < accessPath.size(); i++){
							av.appendField(accessPath.get(i));
						}
						spa.getPathSummary().addAlias(av);
					}else if((tmpTV = spa.getPathSummary().isTaintBase(rv, currUnit)) != null){//issue 3
						InstanceFieldRef ifr = (InstanceFieldRef) tmpTV.getTaintValue();
						AliasValue av = new AliasValue(currUnit, tmpTV, lv);
						av.appendField(ifr.getFieldRef());
						spa.getPathSummary().addAlias(av);
					}
				}
			}
			
			//if this is a assignment: result = *invoke $r0.<classname: return-type method-name (List<type>) (List<parameters)
			//or InvokeStmt: virtualinvoke $r0.<com.demos.flowdroid1.MainActivity: void setContentView(int)>(2130903040);
			InvokeExpr invokeExpr = null;
			Value retValue = null;
			if(currUnit instanceof AssignStmt){
				AssignStmt as = (AssignStmt) currUnit;
				if(!issm.isSource(as, icfg)){
					Value rv = as.getRightOp();
					if(rv instanceof InvokeExpr)
						invokeExpr = (InvokeExpr) rv;
					if(invokeExpr != null){
						retValue = as.getLeftOp();
					}
				}
			}else if(currUnit instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt) currUnit;
				invokeExpr = is.getInvokeExpr();
			}
			
			if(invokeExpr != null && !spa.getPathSummary().invokeExparHandled(invokeExpr)){
				spa.getPathSummary().handledInvokeExpr(invokeExpr);
				SootMethodRef smr = invokeExpr.getMethodRef();
				String className = smr.declaringClass().getName();
				String methodName = smr.name();
				SootMethod callee = AnalysisManager.v().getMethod(className, methodName);
				if(callee != null){
					//this method is in excluedeList, skip it
					if(AnalysisManager.v().isInExcludeList(callee.getDeclaringClass().getName(), methodName)){
						//TODO currently, nothing to do
						//this method is in includeList or classList
					}else if(AnalysisManager.v().isInIncludeSet(callee.getDeclaringClass().getName(), methodName)
							|| AnalysisManager.v().isInClassList(callee.getDeclaringClass().getName(), methodName)){
						//if any one of the parameters is tainted, the retValue shoule be tainted
						//TODO
					}else{
						//start a new SingleMethodAnalysis
						SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.Callee);
						MethodSummary calleeMS = sma.getMethodSummary();
						List<Value> args = invokeExpr.getArgs();
						TaintValue tmpTV = null;
						AliasValue tmpAV = null;
						int argsCount = args.size();
						calleeMS.getMethodInitState().initArgs(argsCount);
						//handle "this"
						if(!callee.isStatic()){
							Value base = ((InstanceInvokeExpr)invokeExpr).getBase();
							if((tmpTV = spa.getPathSummary().isTainted(base, currUnit)) != null
								|| (tmpTV = spa.getPathSummary().isTaintBase(base, currUnit)) != null){
								calleeMS.getMethodInitState().setThisTV(tmpTV);
							}else if((tmpAV = spa.getPathSummary().isAlias(base, currUnit)) != null
									|| (tmpAV = spa.getPathSummary().isAliasBase(base, currUnit)) != null){
								calleeMS.getMethodInitState().addThisAV(tmpAV);
							}
						}
						//handle the args
						for(int i = 0; i < argsCount; i++){
							Value arg = args.get(i);
							if((tmpTV = spa.getPathSummary().isTainted(arg, currUnit)) != null
									|| (tmpTV = spa.getPathSummary().isTaintBase(arg, currUnit)) != null){
								calleeMS.getMethodInitState().setArgTaintValue(i, tmpTV);
							}else if((tmpAV = spa.getPathSummary().isAlias(arg, currUnit)) != null
									|| (tmpAV = spa.getPathSummary().isAliasBase(arg, currUnit)) != null){
								calleeMS.getMethodInitState().addArgAliasValue(i, tmpAV);
							}
						}
						sma.start();
						logger.info("Method {} exit!", sma.getMethod().getName());
					}
				}
				//********* this is a sink ********
				if(issm.isSink((Stmt)currUnit, icfg)){
					List<Value> args = invokeExpr.getArgs();
					for(Value arg : args){
						if(spa.getPathSummary().isTainted(arg, currUnit) != null){
							logger.info("Sink has parameter(s) tainted {} {}", currUnit, arg);
						}
					}
				}
			}
			
			//ret* instructions
			if(currUnit instanceof ReturnStmt){
				ReturnStmt rs = (ReturnStmt) currUnit;
				Value retV = rs.getOp();
				TaintValue retTV = null;
				//rv is tainted
				if((retTV = spa.getPathSummary().isTainted(retV, currUnit)) != null){
					spa.getPathSummary().getSinglePathExitState().setRetTV(retTV);
				}
				//rv is an alias
				ArrayList<AliasValue> retAVs = spa.getPathSummary().getAllAliases(retV, currUnit);
				spa.getPathSummary().getSinglePathExitState().addAllRetAVs(retAVs);
			}
			
			currIndex++;
		}
	}
	
	private void foundNewTaint(Unit currUnit, Value lv){
		if(spa.getPathSummary().alreadyInTaintsSet(currUnit, lv)){
			return;
		}
		//first add the left value to taints set
		TaintValue tv = new TaintValue(currUnit, lv);
		spa.getPathSummary().addTaintValue(tv);
		//then, whether the left value is a FieldRef (only instance field can have alias) TODO
		if(lv instanceof InstanceFieldRef){
			tv.setHeapAssignment(true);
			BackwardAnalysis ba = new BackwardAnalysis(currUnit, tv, spa);
			ba.startBackward();
		}
	}

}
