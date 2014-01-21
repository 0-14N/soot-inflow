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

import soot.PrimType;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;

public class AliasBackwardAnalysis {
	private static AliasBackwardAnalysis instance;
	
	Logger logger = LoggerFactory.getLogger(getClass());
	private final boolean debug = true;

	private IInfoflowCFG icfg; 
	private static HashMap<Block, Set<Unit>> sources;
	
	private AliasBackwardAnalysis(){};
	
	public static AliasBackwardAnalysis v(){
		if(instance == null){
			instance = new AliasBackwardAnalysis();
			sources = new HashMap<Block, Set<Unit>>();
		}
		return instance;
	}
	
	public void setICFG(IInfoflowCFG iCfg){
		this.icfg = iCfg;
	}
	
	public void addSource(Block b, Unit u){
		Set<Unit> set = sources.get(b);
		if(set == null)
			set = new HashSet<Unit>();
		set.add(u);
		sources.put(b, set);
	}
	
	public void start(){
		Iterator<Entry<Block, Set<Unit>>> iter = sources.entrySet().iterator();
		while(iter.hasNext()){
			Map.Entry<Block, Set<Unit>> entry = (Entry<Block, Set<Unit>>) iter.next();
			Block b = entry.getKey();
			Set<Unit> set = entry.getValue();
			
			for(Unit u : set){
				if(debug)
					logger.info("source: {}====>{}", u.getClass(), u);
				//if the source is a method call, currently we only care
				//about the return of the call, so only the lfetOp is tainted
				if(u instanceof AssignStmt){
					AssignStmt s = (AssignStmt) u;
					Value leftOp = s.getLeftOp();
					SootMethod m = icfg.getMethodOf(u);
					ArrayList<ArrayList<Block>> paths = MethodPathCreator.v().getPaths(m);
				}

			}
		}
	}
	
	
	/**
	 * 1. First we start forward analysis from the activation unit to find some heap assignment:
	 * 	  for example, s.g = t (t is tainted), then we label s.g is tainted and began
	 * 	  backward analysis to find the alias of "s.g"
	 * 2. Continue backward analysis until the start point of the method. Record the alias related
	 * 	  to parameters, instance fields, static fields, return value.
	 * 3. Continue forward analysis from the last heap assignment.
	 * 4. loop step 1 to step 3
	 * @param m method contains the source
	 * @param activationUnit the source unit
	 * @param taintedValue the value was tainted at source
	 */
	private void analyzeAliasForSingleMethod(Block b, Unit activationUnit, Value taintedValue){
		ClassicCompleteBlockGraph ccbg = new ClassicCompleteBlockGraph(b.getBody());
		List<Block> blocks = ccbg.getBlocks();
		Iterator<Unit> iter = b.iterator();
		
		//store this block's units to a list, look up conveniently
		ArrayList<Unit> unitList = new ArrayList<Unit>(); 
		while(iter.hasNext()){
			Unit u = iter.next();
			unitList.add(u);
		}
		
		int activationIndex = unitList.indexOf(activationUnit);
		analyzeAliasForSingleBlock(unitList, activationIndex, taintedValue);
	}

	/**
	 * alias analysis for a single block
	 * Algorithm:
	 * 1. start from the stmt at activationIndex, when we meet a heap assignment stmt, go to step 2
	 * 2. backward from the heap assignment stmt
	 * @param unitList
	 * @param activationIndex
	 * @param taintedValue
	 */
	private void analyzeAliasForSingleBlock(ArrayList<Unit> unitList, int activationIndex, Value taintedValue){
		int size = unitList.size();
		int i = 0;
		for(i = activationIndex; i < size; i++){
			Unit u = unitList.get(i);
			if(u instanceof AssignStmt){
				AssignStmt s = (AssignStmt) u;
				triggerBackwardAliasAnalysis(s.getLeftOp());
			}
		}
	}

	/**
	 * whether this value is a instance field or class field.
	 * if the value is a field type, return true.
	 * TODO: ArrayRef
	 * @param v
	 * @return
	 */
	private boolean triggerBackwardAliasAnalysis(Value v){
		assert(v != null);
		if(((v instanceof InstanceFieldRef) || (v instanceof StaticFieldRef))){ //&& //InstanceFieldRef or StaticFieldRef
				//(!(v.getType() instanceof PrimType)) && //not primType
				//(!(v.getType().getClass().getName().equals("java.lang.String")))){ //not String
			return true;
		}
		return false;
	}
}






























