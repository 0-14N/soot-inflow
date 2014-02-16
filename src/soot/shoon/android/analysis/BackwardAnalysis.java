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
import soot.jimple.FieldRef;
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
import soot.shoon.android.analysis.entity.TaintValue;

public class BackwardAnalysis {

	private Logger logger = LoggerFactory.getLogger(getClass());
	private ISourceSinkManager issm;
	private SinglePathAnalysis spa;
	private Unit activationUnit;
	//w.f = t
	private TaintValue tv;
	private InstanceFieldRef fr;//w.f
	private ArrayList<AliasValue> newAVs;
	
	public BackwardAnalysis(Unit activationUnit, TaintValue tv, 
			SinglePathAnalysis spa){
		this.activationUnit = activationUnit;
		this.spa = spa;
		this.tv = tv;
		this.issm = AnalysisManager.v().getISSM();
		this.newAVs = new ArrayList<AliasValue>();
	}
	
	
	public void startBackward(){
		int currIndex = spa.getPathSummary().indexOfUnit(activationUnit);
		while(currIndex >= 0){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
			
			//if this is activation unit, init fieldref and backward
			if(currUnit == activationUnit){
				this.fr = (InstanceFieldRef) ((DefinitionStmt) currUnit).getLeftOp();
				currIndex--;
				continue;
			}
		
			//[start] DefinitionStmt
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				
				assert(fr != null);
				Value lv = s.getLeftOp();
				Value rv = s.getRightOp();
				Value base = fr.getBase();
				//w.t = tainted, w = x; x = w; w = x.a; x.a = w;
				//newAVs: x.t, x.a.t
				//y = x, y = x.t; x = y; x.t = y;
				if(lv.toString().equals(base.toString()) &&
						(rv instanceof FieldRef || rv instanceof Local)){
					AliasValue av = null;
					if(rv instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) rv;
						Value aliasBase = ifr.getBase();
						av = new AliasValue(currUnit, tv, aliasBase);
						av.appendField(ifr.getFieldRef());
					}else{
						av = new AliasValue(currUnit, tv, rv);
					}
					//av: x.t/x.a.t
					av.appendField(tv.getSootFieldRef());
					spa.getPathSummary().addAlias(av);
					newAVs.add(av);
					ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, av);
					fa.startForward();
				}else if(rv.toString().equals(base.toString()) && 
						(lv instanceof FieldRef || lv instanceof Local)){
					AliasValue av = null; 
					if(lv instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) lv;
						Value aliasBase = ifr.getBase();
						av = new AliasValue(currUnit, tv, aliasBase);
						av.appendField(ifr.getFieldRef());
					}else{
						av = new AliasValue(currUnit, tv, lv);
					}
					av.appendField(tv.getSootFieldRef());
					spa.getPathSummary().addAlias(av);
					newAVs.add(av);
					ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, av);
					fa.startForward();
				}else{
					for(AliasValue newAV : newAVs){
						//TODO it is complicated!
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
							if(thisBase.toString().equals(this.fr.getBase().toString())){
								calleeMS.getMethodInitState().setThisTV(this.tv);
								shouldActivate = true;
							}
						}
						//handle the args
						for(int i = 0; i < argsCount; i++){
							Value arg = args.get(i);
							if(arg.toString().equals(this.fr.getBase().toString())){
								calleeMS.getMethodInitState().setArgTaintValue(i, this.tv);
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
									AliasValue newExitThisAV = new AliasValue(currUnit, this.tv, thisBase);
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
											AliasValue newExitArgAV = new AliasValue(currUnit, this.tv, arg);
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
									AliasValue newExitRetAV = new AliasValue(currUnit, this.tv, retValue);
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
