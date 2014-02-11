package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootClass;
import soot.SootFieldRef;
import soot.SootMethod;
import soot.SootMethodRef;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MergedExitState;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;
import soot.shoon.android.analysis.entity.TaintValue;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;

public class AnalysisManager {
	private static AnalysisManager instance;
	
	Logger logger = LoggerFactory.getLogger(getClass());

	private IInfoflowCFG icfg; 
	private ISourceSinkManager issm;
	private EasyTaintWrapper itpw;
	private static ArrayList<SingleMethodAnalysis> sources;
	private static HashMap<Block, Set<Unit>> sinks;
	private static HashMap<SootClass, Set<SootMethod>> allReachableMethods;

	//EasyTaintWrapper related
	private Map<String, List<String>> classList;
	private Map<String, List<String>> excludeList;
	private Map<String, List<String>> killList;
	private Set<String> includeSet;

	//this list records all the methods appear at 'source' path, which is used to
	//exclude the 'sink' path contains source
	private ArrayList<SootMethod> methodsAtSourcePath = new ArrayList<SootMethod>();
	
	private AnalysisManager(){};
	
	public static AnalysisManager v(){
		if(instance == null){
			instance = new AnalysisManager();
			sources = new ArrayList<SingleMethodAnalysis>();
			sinks = new HashMap<Block, Set<Unit>>();
			allReachableMethods = new HashMap<SootClass, Set<SootMethod>>();
		}
		return instance;
	}
	
	public void setICFG(IInfoflowCFG iCfg){
		this.icfg = iCfg;
	}
	
	public void setISSM(ISourceSinkManager issm){
		this.issm = issm;
	}
	
	public void setITPW(ITaintPropagationWrapper itpw){
		assert(itpw instanceof EasyTaintWrapper);
		this.itpw = (EasyTaintWrapper) itpw;
		this.classList = this.itpw.getClassList();
		this.excludeList = this.itpw.getExcludeList();
		this.killList = this.itpw.getKillList();
		this.includeSet = this.itpw.getIncludeList();
	}
	
	public IInfoflowCFG getICFG(){
		return this.icfg;
	}
	
	public ISourceSinkManager getISSM(){
		return this.issm;
	}
	
	public EasyTaintWrapper getITPW(){
		return this.itpw;
	}
	
	public void addSource(SingleMethodAnalysis sma){
		sources.add(sma);
	}
	
	
	public void addSink(Block b, Unit u){
		Set<Unit> set = sinks.get(b);
		if(set == null)
			set = new HashSet<Unit>();
		set.add(u);
		sinks.put(b, set);
	}
	
	public void addMethod(SootMethod sm){
		SootClass sc = sm.getDeclaringClass();
		Set<SootMethod> set = allReachableMethods.get(sc);
		if(set == null)
			set = new HashSet<SootMethod>();
		set.add(sm);
		allReachableMethods.put(sc, set);
	}

	//start analysis at methods that contain statements invoke source
	public void start(){
		//first start 'source' path backward analysis
		for(SingleMethodAnalysis sma : sources){
			//save the methods appear on 'source' path
			methodsAtSourcePath.add(sma.getMethod());
			sma.start();
			sma.getMethodSummary().mergePathSummaries();
			MergedExitState mes = sma.getMethodSummary().getMergedExitState();
			ArrayList<SingleMethodAnalysis> callers = getCallersOf(sma.getMethod());
			backwardToEntry(callers, mes);
		}
		
		//get the dummyMain method
		assert(dummyMain != null);

		/*
		//then, we should find the 'sink' path, also, we should exclude those paths
		//have been analyzed because that they contain both source and sink
		Iterator sinkIter = sinks.entrySet().iterator();
		while(sinkIter.hasNext()){
			Entry<Block, Set<Unit>> entry = (Entry<Block, Set<Unit>>) sinkIter.next();
			Block block = entry.getKey();
			SootMethod sinkContainer = block.getBody().getMethod();
			collectSinkTriggerUnis(sinkContainer, null);
		}
	
		//this is the tmp path summary, which is used to store the states of all 'source' path states
		PathSummary tmpSummary = new PathSummary(null);
		Iterator sourcePathExitStateIter = allSourcePathExitStates.entrySet().iterator();
		while(sourcePathExitStateIter.hasNext()){
			Entry<Unit, Set<MergedExitState>> entry = (Entry<Unit, Set<MergedExitState>>) sourcePathExitStateIter.next();
			Unit sourceTriggerUnit = entry.getKey();
			Set<MergedExitState> exitStateSet = entry.getValue();
			collectSourceExitStates(tmpSummary, sourceTriggerUnit, exitStateSet);
		}
		
		//get the invoke units except the source and sink triggers
		assert(dummyMain != null);
		Set<Unit> allCallSites = icfg.getCallsFromWithin(dummyMain);
		ArrayList<Unit> normalCallSites = new ArrayList<Unit>();
		Set<Unit> sourceTrigger = allSourcePathExitStates.keySet();
		for(Unit callSite : allCallSites){
			if(!sourceTrigger.contains(callSite) && !sinkTriggerUnits.contains(callSite)){
				normalCallSites.add(callSite);
			}
		}
		//start forward normal calls analysis
		for(Unit normalCall : normalCallSites){
			InvokeExpr invokeExpr = null;
			Value thisBase = null;
			Value retValue = null;
			int argsCount = 0;
			List<Value> args = null;
			
			if(normalCall instanceof AssignStmt){
				invokeExpr = (InvokeExpr) ((AssignStmt) normalCall).getRightOp();
				retValue = ((AssignStmt) normalCall).getLeftOp();
			}else if(normalCall instanceof InvokeStmt){
				invokeExpr = ((InvokeStmt) normalCall).getInvokeExpr();
			}
			argsCount = invokeExpr.getArgCount();
			args = invokeExpr.getArgs();
			
			SootMethodRef smr = invokeExpr.getMethodRef();
			String className = smr.declaringClass().getName();
			String methodName = smr.name();
			SootMethod callee = AnalysisManager.v().getMethod(className, methodName);
			
			if(callee != null){
				SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.Callee);
				MethodSummary calleeMS = sma.getMethodSummary();
				calleeMS.getMethodInitState().initArgs(argsCount);
				
				TaintValue tmpTV = null;
				Set<AliasValue> tmpAVs = null;
				//this's taint value and alias values
				if(!callee.isStatic()){
					thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
					if((tmpTV = isTainted(tmpSummary.getTaintsSet(), thisBase)) != null){
						calleeMS.getMethodInitState().setThisTV(tmpTV);
					}
					if((tmpAVs = isAliasValue(tmpSummary.getAliasValues(), thisBase)).size() > 0){
						for(AliasValue av : tmpAVs){
							calleeMS.getMethodInitState().addThisAV(av);
						}
					}
				}
				
				//args' taint values and alias values
				for(int i = 0; i < argsCount; i++){
					Value arg = args.get(i);
					if((tmpTV = isTainted(tmpSummary.getTaintsSet(), arg)) != null){
						calleeMS.getMethodInitState().setArgTaintValue(i, tmpTV);
					}
					if((tmpAVs = isAliasValue(tmpSummary.getAliasValues(), arg)).size() > 0){
						for(AliasValue av : tmpAVs){
							calleeMS.getMethodInitState().addArgAliasValue(i, av);
						}
					}
				}
				
				sma.start();
				sma.getMethodSummary().mergePathSummaries();
				MergedExitState mes = sma.getMethodSummary().getMergedExitState();
				addExitState(tmpSummary, mes, thisBase, argsCount, args, retValue);
			}
		}
		
			
		//start forward 'sink' path analysis
		for(Unit sinkTriggerUnit : sinkTriggerUnits){
			assert(sinkTriggerUnit instanceof AssignStmt || sinkTriggerUnit instanceof InvokeStmt);
			InvokeExpr invokeExpr = null;
			Value thisBase = null;
			int argsCount = 0;
			List<Value> args = null;
			
			if(sinkTriggerUnit instanceof AssignStmt){
				invokeExpr = (InvokeExpr) ((AssignStmt) sinkTriggerUnit).getRightOp();
			}else if(sinkTriggerUnit instanceof InvokeStmt){
				invokeExpr = ((InvokeStmt) sinkTriggerUnit).getInvokeExpr();
			}
			assert(invokeExpr != null);
			argsCount = invokeExpr.getArgCount();
			args = invokeExpr.getArgs();
		
			//get the callee on sink path
			SootMethodRef smr = invokeExpr.getMethodRef();
			String className = smr.declaringClass().getName();
			String methodName = smr.name();
			SootMethod callee = AnalysisManager.v().getMethod(className, methodName);
			
			if(callee != null){
				SingleMethodAnalysis sma = new SingleMethodAnalysis(callee, MethodAnalysisType.Callee);
				MethodSummary calleeMS = sma.getMethodSummary();
				calleeMS.getMethodInitState().initArgs(argsCount);
				
				//add static fields' tvs and avs
				calleeMS.getMethodInitState().addAllStaticFieldTVs(tmpSummary.getStaticFieldTVs());
				calleeMS.getMethodInitState().addAllStaticFieldAVs(tmpSummary.getStaticFieldAVs());
		
				TaintValue tmpTV = null;
				Set<AliasValue> tmpAVs = null;
				//this's taint value and alias values
				if(!callee.isStatic()){
					thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
					if((tmpTV = isTainted(tmpSummary.getTaintsSet(), thisBase)) != null){
						calleeMS.getMethodInitState().setThisTV(tmpTV);
					}
					if((tmpAVs = isAliasValue(tmpSummary.getAliasValues(), thisBase)).size() > 0){
						for(AliasValue av : tmpAVs){
							calleeMS.getMethodInitState().addThisAV(av);
						}
					}
				}
				
				//args' taint values and alias values
				for(int i = 0; i < argsCount; i++){
					Value arg = args.get(i);
					if((tmpTV = isTainted(tmpSummary.getTaintsSet(), arg)) != null){
						calleeMS.getMethodInitState().setArgTaintValue(i, tmpTV);
					}
					if((tmpAVs = isAliasValue(tmpSummary.getAliasValues(), arg)).size() > 0){
						for(AliasValue av : tmpAVs){
							calleeMS.getMethodInitState().addArgAliasValue(i, av);
						}
					}
				}
				
				sma.start();
			}
		}
	
		*/
	}
	
	private TaintValue isTainted(Set<TaintValue> taintsSet, Value value){
		TaintValue result = null;
		for(TaintValue tv : taintsSet){
			if(tv.getTaintValue().toString().equals(value.toString())){
				result = tv;
				break;
			}
		}
		return result;
	}
	
	private Set<AliasValue> isAliasValue(Set<AliasValue> aliasSet, Value value){
		Set<AliasValue> result = new HashSet<AliasValue>();
		for(AliasValue av : aliasSet){
			if(value instanceof InstanceFieldRef){
				ArrayList<SootFieldRef> accessPath = av.getAccessPath();
				if(accessPath != null && accessPath.size() > 0){
					InstanceFieldRef ifr = (InstanceFieldRef) value;
					Value base = ifr.getBase();
					SootFieldRef sfr = ifr.getFieldRef();
					if(av.getAliasBase().toString().equals(base.toString()) &&
							accessPath.get(0).toString().equals(sfr.toString())){
						result.add(av);
					}
				}
			}else{
				if(av.getAliasBase().toString().equals(value.toString())){
					result.add(av);
				}
			}
		}
		return result;
	}
	
	private void collectSourceExitStates(PathSummary tmpSummary, Unit sourceTrigger, Set<MergedExitState> stateSet){
		assert(sourceTrigger instanceof AssignStmt || sourceTrigger instanceof InvokeStmt);
		//parse the source trigger
		InvokeExpr invokeExpr = null;
		Value thisBase = null;
		Value retValue =  null;
		int argsCount = 0;
		List<Value> args = null;
		if(sourceTrigger instanceof AssignStmt){
			AssignStmt as = (AssignStmt) sourceTrigger;
			retValue = as.getLeftOp();
			invokeExpr = (InvokeExpr) as.getRightOp();
		}else if(sourceTrigger instanceof InvokeStmt){
			invokeExpr = ((InvokeStmt) sourceTrigger).getInvokeExpr();
		}
		assert(invokeExpr != null);
		if(invokeExpr instanceof InstanceInvokeExpr){
			thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
		}
		argsCount = invokeExpr.getArgCount();
		args = invokeExpr.getArgs();
		

		for(MergedExitState mes : stateSet){
			addExitState(tmpSummary, mes, thisBase, argsCount, args, retValue);
		}
	}
	
	private void addExitState(PathSummary tmpSummary, MergedExitState mes, 
			Value thisBase, int argsCount, List<Value> args, Value retValue){
		//get the exit state
		TaintValue thisTV = mes.getMergedExitThisTV();
		ArrayList<AliasValue> thisAVs = mes.getMergedExitThisAVs();
		ArrayList<TaintValue> argsTVs = mes.getMergedExitArgTVs();
		ArrayList<ArrayList<AliasValue>> argsAVs = mes.getMergedExitArgAVs();
		TaintValue retTV = mes.getMergedRetTV();
		ArrayList<AliasValue> retAVs = mes.getMergedRetAVs();
		//static fields' avs and tvs
		ArrayList<StaticFieldRef> sfrTVs = mes.getStaticFieldTVs();
		HashMap<StaticFieldRef, Set<AliasValue>> sfrAVs = mes.getStaticFieldAVs();
		
		//add sf's avs and tvs
		tmpSummary.addAllStaticFieldTVs(sfrTVs);
		tmpSummary.addAllStaticFieldAVs(sfrAVs);
			
		
		//this's taint value
		if(thisBase != null && thisTV != null){
			TaintValue newThisTV = new TaintValue(null, thisBase);
			tmpSummary.addTaintValue(newThisTV);
		}
		//this's alias values
		if(thisBase != null && thisAVs != null){
			for(AliasValue thisAV : thisAVs){
				AliasValue newThisAV = new AliasValue(null, null, thisBase);
				ArrayList<SootFieldRef> accessPath = thisAV.getAccessPath();
				for(SootFieldRef sfr : accessPath){
					newThisAV.appendField(sfr);
				}
				tmpSummary.addAlias(newThisAV);
			}
		}
		//args' taint values and alias values
		if(argsCount > 0 && argsTVs != null){
			for(int i = 0; i < argsCount; i++){
				Value arg = args.get(i);
					
				TaintValue argTV = argsTVs.get(i);
				if(argTV != null){
					TaintValue newArgTV = new TaintValue(null, arg);
					tmpSummary.addTaintValue(newArgTV);
				}
					
				ArrayList<AliasValue> argAVs = argsAVs.get(i);
				if(argAVs != null){
					for(AliasValue argAV : argAVs){
						AliasValue newArgAV = new AliasValue(null, null, arg);
						ArrayList<SootFieldRef> accessPath  = argAV.getAccessPath();
						for(SootFieldRef sfr : accessPath){
							newArgAV.appendField(sfr);
						}
						tmpSummary.addAlias(newArgAV);
					}
				}
			}
		}
		//ret's taint value
		if(retValue != null && retTV != null){
			TaintValue newRetTV = new TaintValue(null, retValue);
			tmpSummary.addTaintValue(newRetTV);
		}
		//ret's alias values
		if(retValue != null && retAVs != null){
			for(AliasValue retAV : retAVs){
				AliasValue newRetAV = new AliasValue(null, null, retValue);
				ArrayList<SootFieldRef> accessPath = retAV.getAccessPath();
				for(SootFieldRef sfr : accessPath){
					newRetAV.appendField(sfr);
				}
				tmpSummary.addAlias(newRetAV);
			}
		}
		
	}

	//this list is used to save the sink trigger unis in entry
	private ArrayList<Unit> sinkTriggerUnits = new ArrayList<Unit>();
	private void collectSinkTriggerUnis(SootMethod smOnSinkPath, Unit u){
		if(smOnSinkPath.getName().equals("dummyMainMethod")){
			if(!sinkTriggerUnits.contains(u)){
				sinkTriggerUnits.add(u);
			}
		}
		if(isInMethodsAtSourcePathList(smOnSinkPath)){
			return;
		}else{
			Set<Unit> callerUnits = icfg.getCallersOf(smOnSinkPath);
			for(Unit callUnit : callerUnits){
				collectSinkTriggerUnis(icfg.getMethodOf(callUnit), callUnit);
			}
		}
	}
	
	
	
	private boolean isInMethodsAtSourcePathList(SootMethod sm){
		boolean result = false;
		for(SootMethod smOnSourcePath : methodsAtSourcePath){
			if(smOnSourcePath.getSignature().toString().equals(sm.getSignature())){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private ArrayList<SingleMethodAnalysis> getCallersOf(SootMethod sm){
		ArrayList<SingleMethodAnalysis> smas = new ArrayList<SingleMethodAnalysis>();
		Set<Unit> callerUnits = icfg.getCallersOf(sm);
		for(Unit callerUnit : callerUnits){
			SootMethod caller = icfg.getMethodOf(callerUnit);
			ClassicCompleteBlockGraph ccbg = new ClassicCompleteBlockGraph(caller.getActiveBody());
			Block activationBlock = null;
			Iterator<Block> blockIter = ccbg.iterator();
			while(blockIter.hasNext() && activationBlock == null){
				Block b = blockIter.next();
				Iterator<Unit> unitIter = b.iterator();
				while(unitIter.hasNext() && activationBlock == null){
					Unit u = unitIter.next();
					if(u == callerUnit){
						activationBlock = b;
						break;
					}
				}
			}
			SingleMethodAnalysis sma = new SingleMethodAnalysis(caller, activationBlock, callerUnit, MethodAnalysisType.Caller);
			smas.add(sma);
		}
		return smas;
	}

	//this map is used to save the exit states of each 'source' path
	HashMap<Unit, Set<MergedExitState>> allSourcePathExitStates = new HashMap<Unit, Set<MergedExitState>>();
	SootMethod dummyMain = null;
	//analyze backwards from source to entry point
	private void backwardToEntry(ArrayList<SingleMethodAnalysis> callers, MergedExitState mes){
		//comes to the entry point
		if(callers.size() == 1 && callers.get(0).getMethod().getName().equals("dummyMainMethod")){
			if(dummyMain == null){
				dummyMain = callers.get(0).getMethod();
			}
			
			//save the exit state of this 'source' path
			Unit sourceTriggerUnit = callers.get(0).getActivationUnit();
			logger.info("Arrived at dummy method -- {}", sourceTriggerUnit);
			
			SingleMethodAnalysis dummyMain = callers.get(0);
			dummyMain.setMethodAnalysisType(MethodAnalysisType.DummyMain);
			dummyMain.setExitState(mes);
			dummyMain.start();
			
			/*
			Set<MergedExitState> exitStateSet = allSourcePathExitStates.get(sourceTriggerUnit);
			if(exitStateSet == null){
				exitStateSet = new HashSet<MergedExitState>();
				exitStateSet.add(mes);
				allSourcePathExitStates.put(sourceTriggerUnit, exitStateSet);
			}else{
				exitStateSet.add(mes);
			}
			*/
		}else{
			for(SingleMethodAnalysis caller : callers){
				//save the methods appear on 'source' path
				methodsAtSourcePath.add(caller.getMethod());
				caller.setExitState(mes);
				caller.start();
				caller.getMethodSummary().mergePathSummaries();
				MergedExitState callerMES = caller.getMethodSummary().getMergedExitState();
				ArrayList<SingleMethodAnalysis> preCallers = getCallersOf(caller.getMethod());
				backwardToEntry(preCallers, callerMES);
			}
		}
	}
	
	private boolean isInMap(Map<String, List<String>> targetMap, String className, String methodName){
		boolean result = false;
		for(Entry<String, List<String>> entry : targetMap.entrySet()){
			String key = entry.getKey();
			if(key.equals(className)){
				List<String> methodNames = entry.getValue();
				for(String name : methodNames){
					if(name.equals(methodName)){
						result = true;
						break;
					}
				}
			}
		}
		return result;
	}
	
	public boolean isInClassList(String className, String methodName){
		return isInMap(classList, className, methodName);
	}
	
	public boolean isInExcludeList(String className, String methodName){
		return isInMap(excludeList, className, methodName);
	}
	
	public boolean isInKillList(String className, String methodName){
		return isInMap(killList, className, methodName);
	}
	
	public boolean isInIncludeSet(String className, String methodName){
		boolean result = false;
		for(String name : includeSet){
			if(className.startsWith(name)){
				result = true;
				break;
			}
		}
		return result;
	}

	private SootClass getSootClass(String className){
		SootClass result = null;
		for(Entry<SootClass, Set<SootMethod>> entry : allReachableMethods.entrySet()){
			SootClass sc = entry.getKey();
			if(className.equals(sc.getName())){
				result = sc;
				break;
			}
		}
		assert(result != null);
		return result;
	}
	
	public SootMethod getMethod(String className, String methodName){
		SootMethod result = null;
		for(Entry<SootClass, Set<SootMethod>> entry : allReachableMethods.entrySet()){
			SootClass sc = entry.getKey();
			if(className.equals(sc.getName())){
				Set<SootMethod> sms = entry.getValue();
				for(SootMethod sm : sms){
					if(methodName.equals(sm.getName())){
						result = sm;
						break;
					}
				}
			}
		}
		if(result == null){
			SootClass sc = getSootClass(className);
			if(sc == null)
				return null;
			if(!sc.hasSuperclass()){
				return null;
			}
			SootClass superClass = sc.getSuperclass();
			if(superClass == null)
				return null;
			else
				return getMethod(superClass.getName(), methodName);
		}
		return result;
	}
}
