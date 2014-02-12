package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.IdentityUnit;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ParameterRef;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MergedExitState;
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
	
		//avoid re-enter the callee
		if(this.spa.getMethodAnalysisType() == MethodAnalysisType.Caller){
			//TODO 14-2-11
			currIndex++;
		}
		
		while(currIndex < stopIndex){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
			
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				
				Value lv = s.getLeftOp();
				Value rv = s.getRightOp();
				
				//[start] callee-initialization
				//initialize the taints and aliases
				if(this.spa.getMethodAnalysisType() == MethodAnalysisType.Callee ||
						this.spa.getMethodAnalysisType() == MethodAnalysisType.AliasValueCallee){
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
				//[end]
			
			
				//[start] common taint propagation
				//if this a source
				Set<AliasValue> tmpAVs = null;
				TaintValue tmpTV = null;
				//if(issm.isSource(s, icfg)){
				if(issm.isMySource(s)){
					if(currAliasValue == null){
						foundNewTaint(currUnit, lv);
					}
				}else if(rv instanceof StaticFieldRef){
					//if rv is a tainted static field
					if(spa.getPathSummary().isStaticFieldTainted((StaticFieldRef) rv) != null){
						foundNewTaint(currUnit, lv);
					}
				
					//get the avs
					Set<AliasValue> avSet = spa.getPathSummary().getStaticFieldAVs((StaticFieldRef) rv);
					if(avSet != null && avSet.size() > 0){
						for(AliasValue av : avSet){
							AliasValue newAV = new AliasValue(currUnit, null, rv);
							ArrayList<SootFieldRef> accessPath = av.getAccessPath();
							for(SootFieldRef sfr : accessPath){
								newAV.appendField(sfr);
							}
							spa.getPathSummary().addAlias(newAV);
						}
					}
					
				}else if(spa.getPathSummary().isTainted(rv, currUnit) != null){//rv is in taintsSet
					foundNewTaint(currUnit, lv);
				}else if(spa.getPathSummary().isAlias(rv, currUnit).size() > 0){
					foundNewTaint(currUnit, lv);
				}else{
					// the right value is not tainted
					//if the left value is already tainted
					if((tmpTV = spa.getPathSummary().isTainted(lv, currUnit)) != null){
						if(rv instanceof Constant){
							spa.getPathSummary().deleteTaint(tmpTV);
						}
					}else if((tmpAVs = spa.getPathSummary().isAlias(lv, currUnit)).size() > 0){//if the left value is an alias
						if(rv instanceof Constant){
							for(AliasValue tmpAV : tmpAVs){
								spa.getPathSummary().deleteAlias(tmpAV);
							}
						}
					}
					//if the right value is an alias's base, produce a new alias
					//or 
					//p0.f = tainted_value; ——————————— p0.f is tainted
					//p1 = p0; ————————————————- p1.f is an alias ********************bug issue3
					//sink(p1.f); ————————————————  
					if((tmpAVs = spa.getPathSummary().isAliasBase(rv, currUnit)).size() > 0){
						Value base = null;
						SootFieldRef lvIFR = null;
						if(lv instanceof InstanceFieldRef){
							InstanceFieldRef ifr = (InstanceFieldRef) lv;
							base = ifr.getBase();
							lvIFR = ifr.getFieldRef();
						}else{
							base = lv;
						}
						for(AliasValue tmpAV : tmpAVs){
							AliasValue av = new AliasValue(currUnit, tmpAV.getSource(), base);
							if(lvIFR != null){
								av.appendField(lvIFR);
							}
							int i = 0;
							if(rv instanceof InstanceFieldRef){
								i = 1;
							}
							ArrayList<SootFieldRef> accessPath = tmpAV.getAccessPath();
							for(; i < accessPath.size(); i++){
								av.appendField(accessPath.get(i));
							}
							spa.getPathSummary().addAlias(av);
						}
					}else if((tmpTV = spa.getPathSummary().isTaintBase(rv, currUnit)) != null){//issue 3
						InstanceFieldRef ifr = (InstanceFieldRef) tmpTV.getTaintValue();
						AliasValue av = null;
						//lv maybe an InstanceFieldRef
						if(lv instanceof InstanceFieldRef){
							InstanceFieldRef lifr = (InstanceFieldRef) lv;
							av = new AliasValue(currUnit, tmpTV, lifr.getBase());
							av.appendField(lifr.getFieldRef());
						}else{
							av = new AliasValue(currUnit, tmpTV, lv);
						}
						av.appendField(ifr.getFieldRef());
						spa.getPathSummary().addAlias(av);
					}
					
					if(this.spa.getMethodAnalysisType() == MethodAnalysisType.AliasValueCallee){
						if((tmpAVs = spa.getPathSummary().isAliasBase(lv, currUnit)).size() > 0){
							Value base = null;
							SootFieldRef rvIFR = null;
							if(rv instanceof InstanceFieldRef){
								InstanceFieldRef ifr = (InstanceFieldRef) rv;
								base = ifr.getBase();
								rvIFR = ifr.getFieldRef();
							}else{
								base = rv;
							}
							for(AliasValue tmpAV : tmpAVs){
								AliasValue av = new AliasValue(currUnit, tmpAV.getSource(), base);
								if(rvIFR != null){
									av.appendField(rvIFR);
								}
								int i = 0;
								if(lv instanceof InstanceFieldRef){
									i = 1;
								}
								ArrayList<SootFieldRef> accessPath = tmpAV.getAccessPath();
								for(; i < accessPath.size(); i++){
									av.appendField(accessPath.get(i));
								}
								spa.getPathSummary().addAlias(av);
							}
						}else if((tmpTV = spa.getPathSummary().isTaintBase(lv, currUnit)) != null){
							InstanceFieldRef ifr = (InstanceFieldRef) tmpTV.getTaintValue();
							AliasValue av = null;
							//rv maybe an InstanceFieldRef
							if(rv instanceof InstanceFieldRef){
								InstanceFieldRef rifr = (InstanceFieldRef) rv;
								av = new AliasValue(currUnit, tmpTV, rifr.getBase());
								av.appendField(rifr.getFieldRef());
							}else{
								av = new AliasValue(currUnit, tmpTV, rv);
							}
							av.appendField(ifr.getFieldRef());
							spa.getPathSummary().addAlias(av);
						}
					}
				}
				//[end] common taint propagation
			}
		
			//[start] method invoking
			//if this is a assignment: result = *invoke $r0.<classname: return-type method-name (List<type>) (List<parameters)
			//or InvokeStmt: virtualinvoke $r0.<com.demos.flowdroid1.MainActivity: void setContentView(int)>(2130903040);
			InvokeExpr invokeExpr = null;
			Value retValue = null;
			List<Value> args = null;
			int argsCount = 0;
			Value base = null;
			
			if(currUnit instanceof AssignStmt){
				AssignStmt as = (AssignStmt) currUnit;
				//if(!issm.isSource(as, icfg)){
				if(!issm.isMySource(as)){
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
				//TODO need enhancement! it is invalid!
				spa.getPathSummary().handledInvokeExpr(invokeExpr);
				
				args = invokeExpr.getArgs();
				argsCount = args.size();
						
				SootMethodRef smr = invokeExpr.getMethodRef();
				String className = smr.declaringClass().getName();
				String methodName = smr.name();
				SootMethod callee = AnalysisManager.v().getMethod(className, methodName);
			
				if(callee == null){
					//TODO it is weird that some methods are missing in Soot
				}else{
					if(AnalysisManager.v().isInExcludeList(className, methodName)){
						//this method is in excluedeList, skip it
						//TODO currently, nothing to do
					}else if(AnalysisManager.v().isInIncludeSet(className, methodName)){
						//if any one of the parameters is tainted, the retValue should be tainted
						if(retValue != null){
							boolean hasTaintedArg = false;
							for(Value arg : args){
								if(spa.getPathSummary().isTainted(arg, currUnit) != null){
									hasTaintedArg = true;
									TaintValue newTV = new TaintValue(currUnit, retValue);
									spa.getPathSummary().addTaintValue(newTV);
									break;
								}
							}
							if(!hasTaintedArg && !callee.isStatic()){
								base = ((InstanceInvokeExpr) invokeExpr).getBase();
								if(spa.getPathSummary().isTainted(base, currUnit) != null){
									TaintValue newTV = new TaintValue(currUnit, retValue);
									spa.getPathSummary().addTaintValue(newTV);
								}
							}
						}
					}else if(AnalysisManager.v().isInClassList(className, methodName)){
						//TODO
					}else{
						//start a new SingleMethodAnalysis
						SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.Callee);
						MethodSummary calleeMS = sma.getMethodSummary();
						TaintValue tmpTV = null;
						Set<AliasValue> tmpAVs = null;
						calleeMS.getMethodInitState().initArgs(argsCount);
						
						//transfer the static fields' taint values and alias values
						calleeMS.getMethodInitState().addAllStaticFieldTVs(spa.getPathSummary().getStaticFieldTVs());
						calleeMS.getMethodInitState().addAllStaticFieldAVs(spa.getPathSummary().getStaticFieldAVs());
						
						//handle "this"
						if(!callee.isStatic()){
							base = ((InstanceInvokeExpr)invokeExpr).getBase();
							if((tmpTV = spa.getPathSummary().isTainted(base, currUnit)) != null
								|| (tmpTV = spa.getPathSummary().isTaintBase(base, currUnit)) != null){
								calleeMS.getMethodInitState().setThisTV(tmpTV);
							}else if((tmpAVs = spa.getPathSummary().isAlias(base, currUnit)).size() > 0
									|| (tmpAVs = spa.getPathSummary().isAliasBase(base, currUnit)).size() > 0){
								for(AliasValue tmpAV : tmpAVs){
									calleeMS.getMethodInitState().addThisAV(tmpAV);
								}
							}
						}
						//handle the args
						for(int i = 0; i < argsCount; i++){
							Value arg = args.get(i);
							if((tmpTV = spa.getPathSummary().isTainted(arg, currUnit)) != null
									|| (tmpTV = spa.getPathSummary().isTaintBase(arg, currUnit)) != null){
								calleeMS.getMethodInitState().setArgTaintValue(i, tmpTV);
							}else if((tmpAVs = spa.getPathSummary().isAlias(arg, currUnit)).size() > 0
									|| (tmpAVs = spa.getPathSummary().isAliasBase(arg, currUnit)).size() > 0){
								for(AliasValue tmpAV : tmpAVs){
									calleeMS.getMethodInitState().addArgAliasValue(i, tmpAV);
								}
							}
						}
						
						//start the callee analysis and merge the path summaries
						sma.start();
						sma.getMethodSummary().mergePathSummaries();
						
						//next, we should merge callee's exit state with caller's current path state
						MergedExitState calleeMES = sma.getMethodSummary().getMergedExitState();
						ArrayList<StaticFieldRef> sfrTVs = calleeMES.getStaticFieldTVs();
						HashMap<StaticFieldRef, Set<AliasValue>> sfrAVs = calleeMES.getStaticFieldAVs();
						TaintValue exitThisTV = calleeMES.getMergedExitThisTV();
						ArrayList<AliasValue> exitThisAVs = calleeMES.getMergedExitThisAVs();
						ArrayList<TaintValue> exitArgTVs = calleeMES.getMergedExitArgTVs();
						ArrayList<ArrayList<AliasValue>> exitArgAVs = calleeMES.getMergedExitArgAVs();
						TaintValue exitRetTV = calleeMES.getMergedRetTV();
						ArrayList<AliasValue> exitRetAVs = calleeMES.getMergedRetAVs();
						//the new produced tvs and avs
						Set<TaintValue> newTVs = new HashSet<TaintValue>();
						Set<AliasValue> newAVs = new HashSet<AliasValue>();
						
						//[start] collect result of callee
						//add the static fields' taint values and alias values to this path summary
						spa.getPathSummary().addAllStaticFieldTVs(sfrTVs);
						spa.getPathSummary().addAllStaticFieldAVs(sfrAVs);
						
						//this's return taint value
						if(base != null && exitThisTV != null){
							//this is not tainted before invoking, taints it
							if(spa.getPathSummary().isTainted(base, currUnit) == null){
								TaintValue newExitThisTV = new TaintValue(currUnit, base);
								if(spa.getPathSummary().addTaintValue(newExitThisTV)){
									newTVs.add(newExitThisTV);
								}
							}
						}
						//this's return alias values
						if(base != null && exitThisAVs.size() > 0){
							for(AliasValue av : exitThisAVs){
								AliasValue newExitThisAV = new AliasValue(currUnit, null, base);
								ArrayList<SootFieldRef> accessPath = av.getAccessPath();
								for(SootFieldRef sfr : accessPath){
									newExitThisAV.appendField(sfr);
								}
								if(spa.getPathSummary().addAlias(newExitThisAV)){
									newAVs.add(newExitThisAV);
								}
							}
						}
						//args' return taint values & args' return alias values
						if(argsCount > 0){
							for(int i = 0; i < argsCount; i++){
								Value arg = args.get(i);
								//taint values
								TaintValue argTV = exitArgTVs.get(i);
								if(argTV != null){
									if(spa.getPathSummary().isTainted(arg, currUnit) == null){
										TaintValue newExitArgTV = new TaintValue(currUnit, arg);
										if(spa.getPathSummary().addTaintValue(newExitArgTV)){
											newTVs.add(newExitArgTV);
										}
									}
								}
								//alias values
								ArrayList<AliasValue> argAVs = exitArgAVs.get(i);
								if(argAVs != null && argAVs.size() > 0){
									for(AliasValue argAV : argAVs){
										AliasValue newExitArgAV = new AliasValue(currUnit, null, arg);
										ArrayList<SootFieldRef> accessPath = argAV.getAccessPath();
										for(SootFieldRef sfr : accessPath){
											newExitArgAV.appendField(sfr);
										}
										if(spa.getPathSummary().addAlias(newExitArgAV)){
											newAVs.add(newExitArgAV);
										}
									}
								}
							}
						}
						//ret's return taint value
						if(retValue != null && exitRetTV != null){
							if(spa.getPathSummary().isTainted(retValue, currUnit) == null){
								TaintValue newExitRetTV = new TaintValue(currUnit, retValue);
								if(spa.getPathSummary().addTaintValue(newExitRetTV)){
									newTVs.add(newExitRetTV);
								}
							}
						}
						//ret's return alias values
						if(retValue != null && exitRetAVs.size() > 0){
							for(AliasValue av : exitRetAVs){
								AliasValue newExitRetAV = new AliasValue(currUnit, null, retValue);
								ArrayList<SootFieldRef> accessPath = av.getAccessPath();
								for(SootFieldRef sfr : accessPath){
									newExitRetAV.appendField(sfr);
								}
								if(spa.getPathSummary().addAlias(newExitRetAV)){
									newAVs.add(newExitRetAV);
								}
							}
						}
						//[end]
				
						
						//after collect the result, for the new produced tvs and av, should do
						//backward analysis
						for(TaintValue ntv : newTVs){
							Value v = ntv.getTaintValue();
							if(v instanceof InstanceFieldRef){
								ntv.setHeapAssignment(true);
								BackwardAnalysis ba = new BackwardAnalysis(currUnit, ntv, spa);
								ba.startBackward();
							}
						}
						
						for(AliasValue nav : newAVs){
							AVBackwardAnalysis avba = new AVBackwardAnalysis(spa, nav, currUnit);
							avba.startAVBackward();
						}
					}
				}
				
				//********* this is a sink ********
				//if(issm.isSink((Stmt)currUnit, icfg)){
				if(issm.isMySink((Stmt)currUnit)){
					for(Value arg : args){
						if(spa.getPathSummary().isTainted(arg, currUnit) != null){
							logger.info("Sink has parameter(s) tainted {} {}", currUnit, arg);
						}
					}
				}
				
			}
			//[end] method invoking
			
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
