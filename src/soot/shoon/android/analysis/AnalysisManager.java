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
import soot.toolkits.graph.ZonedBlockGraph;

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
	private Map<String, List<String>> noRetWrapperList;

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
		this.noRetWrapperList = new HashMap<String, List<String>>();
		
		//temporarily, we add special cases at here
		ArrayList<String> mapMethods = new ArrayList<String>();
		mapMethods.add("put");
		this.noRetWrapperList.put("java.util.Map", mapMethods);
		ArrayList<String> listMethods = new ArrayList<String>();
		listMethods.add("add");
		this.noRetWrapperList.put("java.util.List", listMethods);
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
		//find the 'source' trigger units in dummyMain
		for(SingleMethodAnalysis sma : sources){
			collectSourceTriggerUnits(sma.getMethod(), null);
		}
		
		//find the 'sink' trigger units in dummyMain
		Iterator sinkIter = sinks.entrySet().iterator();
		while(sinkIter.hasNext()){
			Entry<Block, Set<Unit>> entry = (Entry<Block, Set<Unit>>) sinkIter.next();
			Block block = entry.getKey();
			SootMethod sinkContainer = block.getBody().getMethod();
			collectSinkTriggerUnits(sinkContainer, null);
		}
		
		//first start 'source' path backward analysis
		for(SingleMethodAnalysis sma : sources){
			//save the methods appear on 'source' path
			logger.info("Begin at source \"{}.{}: {}\"", 
					sma.getMethod().getDeclaringClass().getName(), sma.getMethod().getName(), sma.getActivationUnit());
			methodsAtSourcePath.add(sma.getMethod());
			sma.start();
			sma.getMethodSummary().mergePathSummaries();
			MergedExitState mes = sma.getMethodSummary().getMergedExitState();
			ArrayList<SingleMethodAnalysis> callers = getCallersOf(sma.getMethod());
			backwardToEntry(callers, mes);
		}
		
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

	private ArrayList<Unit> sinkTriggerUnits = new ArrayList<Unit>();
	/**
	 * this list is used to save the sink trigger units in dummyMain
	 * @param smOnSinkPath
	 * @param u
	 */
	private void collectSinkTriggerUnits(SootMethod smOnSinkPath, Unit u){
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
				collectSinkTriggerUnits(icfg.getMethodOf(callUnit), callUnit);
			}
		}
	}
	
	public ArrayList<Unit> getSinkTriggerUnits(){
		return this.sinkTriggerUnits;
	}
	
	private ArrayList<Unit> sourceTriggerUnits = new ArrayList<Unit>();
	/**
	 * 
	 * @param smOnSourcePath
	 * @param u
	 */
	private void collectSourceTriggerUnits(SootMethod smOnSourcePath, Unit u){
		if(smOnSourcePath.getName().equals("dummyMainMethod")){
			if(!sourceTriggerUnits.contains(u)){
				sourceTriggerUnits.add(u);
			}
		}
		Set<Unit> callerUnits = icfg.getCallersOf(smOnSourcePath);
		for(Unit callUnit : callerUnits){
			collectSourceTriggerUnits(icfg.getMethodOf(callUnit), callUnit);
		}
	}
	
	public ArrayList<Unit> getSourceTriggerUnits(){
		return this.sourceTriggerUnits;
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
			ZonedBlockGraph zbg = new ZonedBlockGraph(caller.getActiveBody());
			Block activationBlock = null;
			Iterator<Block> blockIter = zbg.iterator();
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
			SingleMethodAnalysis sma = new SingleMethodAnalysis(caller, zbg, activationBlock, callerUnit, MethodAnalysisType.Caller);
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
			logger.info("Back to dummyMain: \"{}\"", sourceTriggerUnit);
			
			SingleMethodAnalysis dummyMain = callers.get(0);
			dummyMain.setMethodAnalysisType(MethodAnalysisType.DummyMain);
			dummyMain.setExitState(mes);
			dummyMain.start();
			
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
	
	public boolean isInNoRetWrapper(String className, String methodName){
		boolean result = false;
		ArrayList<String> methods = (ArrayList<String>) noRetWrapperList.get(className);
		if(methods != null && methods.contains(methodName)){
			result = true;
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
