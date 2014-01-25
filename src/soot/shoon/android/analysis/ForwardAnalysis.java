package soot.shoon.android.analysis;

import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.PathSummary;
import soot.shoon.android.analysis.entity.TaintValue;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;

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
		int length = spa.getPathSummary().getPathLength();
		while(currIndex < length){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				Value lv = s.getLeftOp();
				Value rv = s.getRightOp();
				//if this a source
				if(issm.isSource(s, icfg)){
					foundNewTaint(currUnit, lv);
				}else if(spa.getPathSummary().isTainted(rv, currUnit)){//rv is in taintsSet
					foundNewTaint(currUnit, lv);
				}else if(spa.getPathSummary().isAlias(rv, currUnit)){
					foundNewTaint(currUnit, lv);
				}else{// the right value is not tainted
					//if the left value is already tainted
					if(spa.getPathSummary().isTainted(lv, currUnit)){
						spa.getPathSummary().deleteTaint(lv, currUnit);
					}else if(spa.getPathSummary().isAlias(lv, currUnit)){//if the left value is an alias
						spa.getPathSummary().deleteAlias(lv, currUnit);
					}
					//if the right value is an alias's base, produce a new alias
					AliasValue previousAV;
					if((previousAV = spa.getPathSummary().isAliasBase(rv, currUnit)) != null){
						AliasValue av = new AliasValue(currUnit, previousAV.getSource(), lv, previousAV);
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
						//new SingleMethodAnalysis
						List<Value> args = invokeExpr.getArgs();
						for(Value arg : args){
							if(spa.getPathSummary().isTainted(arg, currUnit)){
							}
						}
						
						SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.Callee);
					}
				}
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
