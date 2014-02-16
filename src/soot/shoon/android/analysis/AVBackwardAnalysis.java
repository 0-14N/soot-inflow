package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Local;
import soot.PointsToSet;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MergedExitState;
import soot.shoon.android.analysis.entity.MethodSummary;

/**
 * @author chenxiong
 *	
 *	p = c; c = p; p = c.f1; c.f1 = p; p.t1 = c; p.t1 = c.f1; c = p.t1; c.f1 = p.t1;
 * 
 * 	p = b; b = p; p = b.f1; b.f1 = p; p.t1 = b; p.t1 = b.f1; b = p.t1; b.f1 = p.t1;	
 * 
 * 	p = a; a = p; p = a.f1; a.f1 = p; p.t1 = a; p.t1 = a.f1; a = p.t1; a.f1 = p.t1;	//XXXXXXXXXXXXXX
 *	a = b.f(c); // a.f1.f2 is tainted, b.f1.f2 is tainted, c.f1 is tainted
 */
public class AVBackwardAnalysis {
	
	private Logger logger = LoggerFactory.getLogger(getClass());
	//[start] variables
	private ISourceSinkManager issm;
	private SinglePathAnalysis spa;
	private AliasValue av;
	private Unit activationUnit;
	private InvokeExpr invokeExpr;
	private ArrayList<AliasValue> newAVs;
	//[end] variables
	
	public AVBackwardAnalysis(SinglePathAnalysis spa, AliasValue av, Unit activationUnit){
		this.spa = spa;
		this.av = av;
		this.activationUnit = activationUnit;
		this.issm = AnalysisManager.v().getISSM();
		this.newAVs = new ArrayList<AliasValue>();
	}
	
	public void startAVBackward(){
		if(activationUnit instanceof AssignStmt){
			AssignStmt as = (AssignStmt) activationUnit;
			Value lv = as.getLeftOp();
			invokeExpr = (InvokeExpr) as.getRightOp();
			if(lv.toString().equals(av.getAliasBase().toString())){
				return;
			}
		}else{
			InvokeStmt is = (InvokeStmt) activationUnit;
			invokeExpr = is.getInvokeExpr();
		}
		
		assert(invokeExpr != null);
		
		int currIndex = spa.getPathSummary().indexOfUnit(activationUnit) - 1;
		
		while(currIndex >= 0){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
			
			//[start] DefinitionStmt
			if(currUnit instanceof DefinitionStmt){
				Value lv = ((DefinitionStmt) currUnit).getLeftOp();
				Value rv = ((DefinitionStmt) currUnit).getRightOp();
				
				if(av.isWithinAccessPath(lv)){
					AliasValue newAV = null;
					if(rv instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) rv;
						newAV = new AliasValue(currUnit, av.getSource(), ifr.getBase());
						newAV.appendField(ifr.getFieldRef());
					}else{
						newAV = new AliasValue(currUnit, av.getSource(), rv);
					}
					int i = 0;
					if(lv instanceof InstanceFieldRef){
						i = 1;
					}
					List<SootFieldRef> accessPath = av.getAccessPath();
					for(; i < accessPath.size(); i++){
						newAV.appendField(accessPath.get(i));
					}
					spa.getPathSummary().addAlias(newAV);
					newAVs.add(newAV);
					ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, newAV);
					fa.startForward();
				}else if(av.isWithinAccessPath(rv)){
					AliasValue newAV = null;
					if(lv instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) lv;
						newAV = new AliasValue(currUnit, av.getSource(), ifr.getBase());
					}else{
						newAV = new AliasValue(currUnit, av.getSource(), lv);
					}
					int i = 0;
					if(rv instanceof InstanceFieldRef){
						i = 1;
					}
					List<SootFieldRef> accessPath = av.getAccessPath();
					for(; i < accessPath.size(); i++){
						newAV.appendField(accessPath.get(i));
					}
					spa.getPathSummary().addAlias(newAV);
					newAVs.add(newAV);
					ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, newAV);
					fa.startForward();
				}else{
					for(AliasValue newAV : newAVs){
						//TODO complicated
					}
				}
			}
			//[end] DefinitionStmt
			
			//[start] method invoking
			InvokeExpr invokeExpr = null;
			Value thisBase = null;
			Value retValue = null;
			int argsCount = 0;
			List<Value> args = null;
			
			if(currUnit instanceof AssignStmt){
				AssignStmt as = (AssignStmt) currUnit;
				if(!issm.isMySource(as) && !issm.isMySink(as)){
					Value rv = as.getRightOp();
					if(rv instanceof InvokeExpr){
						invokeExpr = (InvokeExpr) rv;
						retValue = as.getLeftOp();
					}
				}
			}else if(currUnit instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt) currUnit;
				invokeExpr = is.getInvokeExpr();
			}
			
			if(invokeExpr != null){
				args = invokeExpr.getArgs();
				argsCount = invokeExpr.getArgCount();
				
				SootMethodRef smr = invokeExpr.getMethodRef();
				String className = smr.declaringClass().getName();
				String methodName = smr.name();
				String methodSignature = smr.getSignature();
				SootMethod callee = AnalysisManager.v().getMethod(className, methodName, methodSignature);
				boolean shouldActivate = false;
				
				PointsToSet pts = null;
				Set<Type> types = null;
				if(callee == null && invokeExpr instanceof InstanceInvokeExpr){
					Value itfBase = ((InstanceInvokeExpr) invokeExpr).getBase();
					if(itfBase instanceof Local){
						pts = AnalysisManager.v().getPTA().reachingObjects((Local) itfBase);
					}
				}
				
				if(pts != null){
					types = pts.possibleTypes();
					if(types != null){
						for(Type type : types){
							methodSignature = methodSignature.replaceFirst(className, type.toString());
							className = type.toString();
							callee = AnalysisManager.v().getMethod(className, methodName, methodSignature);
							if(callee != null){
								logger.info("**** found point to {} : {}", className, methodName);
								break;
							}
						}
					}
				}
				
				if(callee != null){
					if(AnalysisManager.v().isInExcludeList(className, methodName)){
						//TODO
					}else if(AnalysisManager.v().isInIncludeSet(className, methodName)){
						//TODO
					}else if(AnalysisManager.v().isInClassList(className, methodName)){
						//TODO
					}else{
						//start a new SingleMethodAnalysis
						SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.AliasValueCallee, this.spa.getSMA());
						MethodSummary calleeMS = sma.getMethodSummary();
						calleeMS.getMethodInitState().initArgs(argsCount);
						
						//transfer the static fields' taint values and alias values
						calleeMS.getMethodInitState().addAllStaticFieldTVs(spa.getPathSummary().getStaticFieldTVs());
						calleeMS.getMethodInitState().addAllStaticFieldAVs(spa.getPathSummary().getStaticFieldAVs());
						
						//handle "this"
						if(!callee.isStatic()){
							thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
							if(av.isWithinAccessPath(thisBase)){
								calleeMS.getMethodInitState().addThisAV(av);
								shouldActivate = true;
							}
						}
						//handle the args
						for(int i = 0; i < argsCount; i++){
							Value arg = args.get(i);
							if(av.isWithinAccessPath(arg)){
								calleeMS.getMethodInitState().addArgAliasValue(i, av);
								shouldActivate = true;
							}
						}
						
						//start the callee analysis and merge the path summaries
						if(shouldActivate){
							sma.start();
							sma.getMethodSummary().mergePathSummaries();
						
							//next, we should merge callee's exit state with caller's current path state
							MergedExitState calleeMES = sma.getMethodSummary().getMergedExitState();
							ArrayList<StaticFieldRef> sfrTVs = calleeMES.getStaticFieldTVs();
							HashMap<StaticFieldRef, Set<AliasValue>> sfrAVs = calleeMES.getStaticFieldAVs();
							//TaintValue exitThisTV = calleeMES.getMergedExitThisTV();
							ArrayList<AliasValue> exitThisAVs = calleeMES.getMergedExitThisAVs();
							//ArrayList<TaintValue> exitArgTVs = calleeMES.getMergedExitArgTVs();
							ArrayList<ArrayList<AliasValue>> exitArgAVs = calleeMES.getMergedExitArgAVs();
							//TaintValue exitRetTV = calleeMES.getMergedRetTV();
							ArrayList<AliasValue> exitRetAVs = calleeMES.getMergedRetAVs();
							//the new produced tvs and avs
							//Set<TaintValue> newTVs = new HashSet<TaintValue>();
							Set<AliasValue> newAVs = new HashSet<AliasValue>();
						
							//[start] collect result of callee
							//add the static fields' taint values and alias values to this path summary
							spa.getPathSummary().addAllStaticFieldTVs(sfrTVs);
							spa.getPathSummary().addAllStaticFieldAVs(sfrAVs);
						
							//this's return alias values
							if(thisBase != null && exitThisAVs.size() > 0){
								for(AliasValue av : exitThisAVs){
									AliasValue newExitThisAV = new AliasValue(currUnit, this.av.getSource(), thisBase);
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
									//alias values
									ArrayList<AliasValue> argAVs = exitArgAVs.get(i);
									if(argAVs != null && argAVs.size() > 0){
										for(AliasValue argAV : argAVs){
											AliasValue newExitArgAV = new AliasValue(currUnit, this.av.getSource(), arg);
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
							//ret's return alias values
							if(retValue != null && exitRetAVs.size() > 0){
								for(AliasValue av : exitRetAVs){
									AliasValue newExitRetAV = new AliasValue(currUnit, this.av.getSource(), retValue);
									ArrayList<SootFieldRef> accessPath = av.getAccessPath();
									for(SootFieldRef sfr : accessPath){
										newExitRetAV.appendField(sfr);
									}
									if(spa.getPathSummary().addAlias(newExitRetAV)){
										newAVs.add(newExitRetAV);
									}
								}
							}
							//[end] collect result of callee
							
							//if there are any new produced avs, do forward analysis
							for(AliasValue newAV : newAVs){
								ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, newAV);
								fa.startForward();
							}
						}
					}
				}
			}
			//[end] method invoking
		
			currIndex--;
		}
	}
}
