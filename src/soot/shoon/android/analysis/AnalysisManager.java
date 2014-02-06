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
import soot.SootMethod;
import soot.Unit;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.MergedExitState;
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
		for(SingleMethodAnalysis sma : sources){
			sma.start();
			sma.getMethodSummary().mergePathSummaries();
			MergedExitState mes = sma.getMethodSummary().getMergedExitState();
			ArrayList<SingleMethodAnalysis> callers = getCallersOf(sma.getMethod());
			backwardToEntry(callers, mes);
		}
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

	//analyze backwards from source to entry point
	private void backwardToEntry(ArrayList<SingleMethodAnalysis> callers, MergedExitState mes){
		//comes to the entry point
		if(callers.size() == 1 && callers.get(0).getMethod().getName().equals("dummyMainMethod")){
			//TODO something	
			logger.info("At Entry Point!!!");
		}else{
			for(SingleMethodAnalysis caller : callers){
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
