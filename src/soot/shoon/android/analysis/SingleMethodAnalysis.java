package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootFieldRef;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.StaticFieldRef;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MergedExitState;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;
import soot.shoon.android.analysis.entity.TaintValue;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ZonedBlockGraph;

public class SingleMethodAnalysis {
	Logger logger = LoggerFactory.getLogger(getClass());
	
	private SootMethod method;
	//private ClassicCompleteBlockGraph ccbg;
	private ZonedBlockGraph zbg;
	private Block activationBlock;
	private Unit activationUnit;
	private MethodAnalysisType type;
	private ArrayList<ArrayList<Block>> paths;
	
	private MethodSummary methodSummary;
	
	//if this is a caller, the exit state of the callee
	private MergedExitState mes = null;
	
	public enum MethodAnalysisType{
		SourceContainer,
		Callee,
		Caller,
		DummyMain,
		AliasValueCallee,
	}

	public SingleMethodAnalysis(SootMethod method, MethodAnalysisType type){
		assert(type == MethodAnalysisType.Callee);
		this.method = method;
		//this.ccbg = new ClassicCompleteBlockGraph(this.method.getActiveBody());
		this.zbg = new ZonedBlockGraph(this.method.getActiveBody());
		//this.activationBlock = this.ccbg.getHeads().get(0);
		this.activationBlock = this.zbg.getHeads().get(0);
		this.activationUnit = this.activationBlock.getHead();
		this.type = type;
		//this.paths = MethodPathCreator.v().getPaths(this.ccbg);
		this.paths = MethodPathCreator.v().getPaths(this.zbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public SingleMethodAnalysis(SootMethod method, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		//this.ccbg = new ClassicCompleteBlockGraph(this.method.getActiveBody());
		this.zbg = new ZonedBlockGraph(this.method.getActiveBody());
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		//this.paths = MethodPathCreator.v().getPaths(this.ccbg);
		this.paths = MethodPathCreator.v().getPaths(this.zbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	//public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit){
	public SingleMethodAnalysis(SootMethod method, ZonedBlockGraph zbg, Block activationBlock, Unit activationUnit){
		this.method = method;
		//this.ccbg = ccbg;
		this.zbg = zbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = MethodAnalysisType.SourceContainer;
		//this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.paths = MethodPathCreator.v().getPaths(this.zbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	//public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
	public SingleMethodAnalysis(SootMethod method, ZonedBlockGraph zbg, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		//this.ccbg = ccbg;
		this.zbg = zbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		//this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.paths = MethodPathCreator.v().getPaths(this.zbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public MethodSummary getMethodSummary(){
		return this.methodSummary;
	}
	
	public Unit getActivationUnit(){
		return this.activationUnit;
	}
	
	public void setExitState(MergedExitState mes){
		assert(this.type == MethodAnalysisType.Caller);
		this.mes = mes;
	}
	
	public void start(){
		//this method contains a source invoking
		if(this.type == MethodAnalysisType.SourceContainer){
			for(ArrayList<Block> path : paths){
				//if(path.contains(activationBlock)){
				if(pathContainsBlock(path, activationBlock)){
					analyzeSinglePath(path);
				}
			}
		}else if(this.type == MethodAnalysisType.Callee || this.type == MethodAnalysisType.AliasValueCallee){
			for(ArrayList<Block> path : paths){
				//if(path.contains(activationBlock)){
				if(pathContainsBlock(path, activationBlock)){
					analyzeSinglePath(path);
				}
			}
		}else if(this.type == MethodAnalysisType.Caller){
			for(ArrayList<Block> path : paths){
				//if(path.contains(activationBlock)){
				if(pathContainsBlock(path, activationBlock)){
					analyzeSinglePath(path);
				}
			}
		}else if(this.type == MethodAnalysisType.DummyMain){
			ArrayList<Block> wholeMethod = new ArrayList<Block>();
			wholeMethod.addAll(this.zbg.getBlocks());
			analyzeSinglePath(wholeMethod);
		}
		//although the code is the same, maybe there will be something specific to be handled
		//in different situations
	}
	
	private boolean pathContainsBlock(ArrayList<Block> path, Block block){
		boolean result = false;
		for(Block b : path){
			if(b.getIndexInMethod() == block.getIndexInMethod()){
				result = true;
				break;
			}
		}
		return result;
	}

	private int getIndexOfBlockStartsUnit(Unit target, ArrayList<Block> path){
		int i = 0;
		for(; i < path.size(); i++){
			Block block = path.get(i);
			Unit head = block.getHead();
			if(head.equals(target)){
				break;
			}
		}
		return i;
	}
	
	private int getIndexOfBlockContainsUnit(Unit u, ArrayList<Block> path){
		int result = 0;
		boolean found = false;
		for(int i = 0; i < path.size() && !found; i++){
			Block block = path.get(i);
			Iterator<Unit> iter = block.iterator();
			while(iter.hasNext() && !found){
				if(iter.next().equals(u)){
					result = i;
					found = true;
				}
			}
		}
		return result;
	}

	private void getChunkOfBlock(int[] labelFlags, int blkIdx, int[] chunk){
		int i = 0;
		
		if(labelFlags[blkIdx] == 1){
			chunk[0] = blkIdx;
			for(i = blkIdx + 1; i < labelFlags.length; i++){
				if(labelFlags[i] == 1) break;
			}
			chunk[1] = i;
		}else{
			for(i = blkIdx; i < labelFlags.length; i++){
				if(labelFlags[i] == 1) break;
			}
			chunk[1] = i;
			for(i = blkIdx; i >= 0; i--){
				if(labelFlags[i] == 1) break;
			}
			if(i == -1) i = 0;
			chunk[0] = i;
		}
	}
	
	private void constructPath(ArrayList<Block> path, int blkIdxOfCurSrTgr,
			int[] labelFlags, int[] sourceFlags, int[] sinkFlags, ArrayList<Unit> allUnits){
		int[] chunk = new int[2];
		int i = 0;
	
		//add the chunk contains curSrTgr first
		getChunkOfBlock(labelFlags, blkIdxOfCurSrTgr, chunk);
		for(i = chunk[0]; i < chunk[1]; i++){
			Block block = path.get(i);
			Iterator<Unit> iter = block.iterator();
			while(iter.hasNext()){
				Unit tmpU = iter.next();
				if(!(tmpU instanceof ReturnStmt) && 
						!(tmpU instanceof ReturnVoidStmt)){
					allUnits.add(tmpU);
				}
			}
		}
		
		//add chunks neither contains source trigger nor contains sink trigger
		for(i = 0; i < path.size(); i = chunk[1]){
			getChunkOfBlock(labelFlags, i, chunk);
			
			boolean containSourceSink = false;
			for(int k = chunk[0]; k < chunk[1]; k++){
				if(sourceFlags[k] == 1 || sinkFlags[k] == 1){
					containSourceSink = true;
					break;
				}
			}
			
			if(!containSourceSink){
				for(int j = chunk[0]; j < chunk[1]; j++){
					Block block = path.get(j);
					Iterator<Unit> iter = block.iterator();
					while(iter.hasNext()){
						Unit tmpU = iter.next();
						if(!(tmpU instanceof ReturnStmt) && 
								!(tmpU instanceof ReturnVoidStmt)){
							allUnits.add(tmpU);
						}
					}
				}
			}
		}
		
		//add chunks contains sink trigger
		for(i = 0; i < sinkFlags.length; i++){
			if(sinkFlags[i] == 1){
				getChunkOfBlock(labelFlags, i, chunk);
				for(int j = chunk[0]; j < chunk[1]; j++){
					Block block = path.get(j);
					Iterator<Unit> iter = block.iterator();
					while(iter.hasNext()){
						Unit tmpU = iter.next();
						if(!(tmpU instanceof ReturnStmt) && 
								!(tmpU instanceof ReturnVoidStmt)){
							allUnits.add(tmpU);
						}
					}
				}
			}
		}
	}
	
	private void analyzeSinglePath(ArrayList<Block> path){
		ArrayList<Unit> allUnits = new ArrayList<Unit>();
		
		if(this.type != MethodAnalysisType.DummyMain){
			for(Block block : path){
				Iterator<Unit> iter = block.iterator();
				while(iter.hasNext()){
					allUnits.add(iter.next());
				}
			}
		}else{
			//TODO dummyMain resort the units
			ArrayList<Unit> sourceTriggerUnits = AnalysisManager.v().getSourceTriggerUnits();
			ArrayList<Unit> sinkTriggerUnits = AnalysisManager.v().getSinkTriggerUnits();
		
			//1. We should split the whole method body to chunks, the 'chunk' some(one or more) blocks of code
			//	starts with "label n" and ends with "label n+1", [label n, label n+1). 
			//2. Note that 'label n' is always target of certain if-stmt.
			//3. If a block's first Unit is target of certain if-stmt, the block should be flagged with '1'
			int[] labelFlags = new int[path.size()];
			for(Block block : path){
				Iterator<Unit> iter = block.iterator();
				while(iter.hasNext()){
					Unit u = iter.next();
					if(u instanceof IfStmt){
						IfStmt sf = (IfStmt) u;
						Unit target = sf.getTarget();
						labelFlags[getIndexOfBlockStartsUnit(target, path)] = 1;
					}
				}
			}
		
			//if a block contains source trigger unit, flagged with '1'
			int[] sourceFlags = new int[path.size()];
			for(Unit sourceTgrU : sourceTriggerUnits){
				sourceFlags[getIndexOfBlockContainsUnit(sourceTgrU, path)] = 1;
			}
			
			//if a block contains sink trigger unit, flagged with '1'
			int[] sinkFlags = new int[path.size()];
			for(Unit sinkTgrU : sinkTriggerUnits){
				int idx = getIndexOfBlockContainsUnit(sinkTgrU, path);
				if(sourceFlags[idx] != 1){
					sinkFlags[idx] = 1;
				}
			}
			
			int blkIdxOfCurSrTgr = getIndexOfBlockContainsUnit(this.activationUnit, path);
			//construct the resorted units of 'dummyMain'
			constructPath(path, blkIdxOfCurSrTgr, labelFlags, sourceFlags, sinkFlags, allUnits);
		}
		
		
		//if this method contains a source invoking
		if(this.type == MethodAnalysisType.SourceContainer){
			PathSummary pSummary = new PathSummary(allUnits);
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}else if(this.type == MethodAnalysisType.Callee || this.type == MethodAnalysisType.AliasValueCallee){
			PathSummary pSummary =  new PathSummary(allUnits);
			pSummary.setInitMethodSummary(methodSummary);
			
			//add the static field's taint and alias values to pSummary
			pSummary.addAllStaticFieldTVs(methodSummary.getMethodInitState().getStaticFieldTVs());
			pSummary.addAllStaticFieldAVs(methodSummary.getMethodInitState().getStaticFieldAVs());
			
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}else if(this.type == MethodAnalysisType.Caller || this.type == MethodAnalysisType.DummyMain){
			assert(mes != null);
			PathSummary pSummary = new PathSummary(allUnits);
			
			//parse the activation unit, it must be an invoking statement
			assert(activationUnit instanceof AssignStmt || activationUnit instanceof InvokeStmt);
			InvokeExpr invokeExpr = null;
			Value thisBase = null;
			Value retValue = null;
			if(activationUnit instanceof AssignStmt){
				AssignStmt as = (AssignStmt) activationUnit;
				Value rv = as.getRightOp();
				assert(rv instanceof InvokeExpr);
				invokeExpr = (InvokeExpr) rv;
				retValue = as.getLeftOp();
			}else if(activationUnit instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt) activationUnit;
				invokeExpr = is.getInvokeExpr();
			}
			assert(invokeExpr != null);
			//instance method invoking, get the base
			if(invokeExpr instanceof InstanceInvokeExpr){
				thisBase = ((InstanceInvokeExpr) invokeExpr).getBase();
			}
			List<Value> args = invokeExpr.getArgs();
			int argsCount = args.size();
			
			//get the callee's exit state
			TaintValue exitThisTV = mes.getMergedExitThisTV();
			ArrayList<AliasValue> exitThisAVs = mes.getMergedExitThisAVs();
			ArrayList<TaintValue> exitArgTVs = mes.getMergedExitArgTVs();
			ArrayList<ArrayList<AliasValue>> exitArgAVs = mes.getMergedExitArgAVs();
			TaintValue exitRetTV = mes.getMergedRetTV();
			ArrayList<AliasValue> exitRetAVs = mes.getMergedRetAVs();
			//static fields' avs and tvs
			ArrayList<StaticFieldRef> sfrTVs = mes.getStaticFieldTVs();
			HashMap<StaticFieldRef, Set<AliasValue>> sfrAVs = mes.getStaticFieldAVs();
		
			//[start] initialize path summary
			//add static fields' avs and tvs
			pSummary.addAllStaticFieldTVs(sfrTVs);
			pSummary.addAllStaticFieldAVs(sfrAVs);
			
			//initialize the callee's exit state to this caller's current path state
			//this's taint value
			if(thisBase != null && exitThisTV != null){
				TaintValue newThisTV = new TaintValue(activationUnit, thisBase);
				pSummary.addTaintValue(newThisTV);
			}
			//this's alias values
			if(thisBase != null && exitThisAVs != null){
				for(AliasValue av : exitThisAVs){
					AliasValue newThisAV = new AliasValue(activationUnit, null, thisBase);
					ArrayList<SootFieldRef> accessPath = av.getAccessPath();
					for(SootFieldRef sfr : accessPath){
						newThisAV.appendField(sfr);
					}
					pSummary.addAlias(newThisAV);
				}
			}
			//args's taint values and alias values
			if(argsCount > 0){
				for(int i = 0; i < argsCount; i++){
					Value arg = args.get(i);
					//taint values
					TaintValue argTV = exitArgTVs.get(i);
					if(argTV != null){
						TaintValue newExitArgTV = new TaintValue(activationUnit, arg);
						pSummary.addTaintValue(newExitArgTV);
					}
					//alias values
					ArrayList<AliasValue> argAVs = exitArgAVs.get(i);
					if(argAVs != null && argAVs.size() > 0){
						for(AliasValue argAV : argAVs){
							AliasValue newExitArgAV = new AliasValue(activationUnit, null, arg);
							ArrayList<SootFieldRef> accessPath = argAV.getAccessPath();
							for(SootFieldRef sfr : accessPath){
								newExitArgAV.appendField(sfr);
							}
							pSummary.addAlias(newExitArgAV);
						}
					}
				}
			}
			//return value's taint value
			if(retValue != null && exitRetTV != null){
				TaintValue newExitRetTV = new TaintValue(activationUnit, retValue);
				pSummary.addTaintValue(newExitRetTV);
			}
			//return value's alias values
			if(retValue != null && exitRetAVs != null){
				for(AliasValue av : exitRetAVs){
					AliasValue newExitRetAV = new AliasValue(activationUnit, null, retValue);
					ArrayList<SootFieldRef> accessPath = av.getAccessPath();
					for(SootFieldRef sfr : accessPath){
						newExitRetAV.appendField(sfr);
					}
					pSummary.addAlias(newExitRetAV);
				}
			}
			//[end]
			
		
			//start the caller's analysis
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}
	}
	
	//public ClassicCompleteBlockGraph getCCBG(){
	//	return this.ccbg;
	//}
	
	public ZonedBlockGraph getZBG(){
		return this.zbg;
	}
	
	public SootMethod getMethod(){
		return this.method;
	}
	
	public void setMethodAnalysisType(MethodAnalysisType mat){
		this.type = mat;
	}
	
}
