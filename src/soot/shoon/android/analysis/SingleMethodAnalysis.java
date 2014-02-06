package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootFieldRef;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MergedExitState;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;
import soot.shoon.android.analysis.entity.TaintValue;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;

public class SingleMethodAnalysis {
	Logger logger = LoggerFactory.getLogger(getClass());
	
	private SootMethod method;
	private ClassicCompleteBlockGraph ccbg;
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
		Caller
	}

	public SingleMethodAnalysis(SootMethod method, MethodAnalysisType type){
		assert(type == MethodAnalysisType.Callee);
		this.method = method;
		this.ccbg = new ClassicCompleteBlockGraph(this.method.getActiveBody());
		this.activationBlock = this.ccbg.getHeads().get(0);
		this.activationUnit = this.activationBlock.getHead();
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(this.ccbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public SingleMethodAnalysis(SootMethod method, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		this.ccbg = new ClassicCompleteBlockGraph(this.method.getActiveBody());
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(this.ccbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = MethodAnalysisType.SourceContainer;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.methodSummary = new MethodSummary(this);
	}
	
	public MethodSummary getMethodSummary(){
		return this.methodSummary;
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
		}else if(this.type == MethodAnalysisType.Callee){
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
	
	private void analyzeSinglePath(ArrayList<Block> path){
		ArrayList<Unit> allUnits = new ArrayList<Unit>();
		for(Block block : path){
			Iterator<Unit> iter = block.iterator();
			while(iter.hasNext()){
				allUnits.add(iter.next());
			}
		}
		
		//if this method contains a source invoking
		if(this.type == MethodAnalysisType.SourceContainer){
			PathSummary pSummary = new PathSummary(allUnits);
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}else if(this.type == MethodAnalysisType.Callee){
			PathSummary pSummary =  new PathSummary(allUnits);
			//TODO pSummay need to be initialized
			pSummary.setInitMethodSummary(methodSummary);
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}else if(this.type == MethodAnalysisType.Caller){
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
		
			//start the caller's analysis
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			methodSummary.addPathSummary(path, pSummary);
		}
	}
	
	public ClassicCompleteBlockGraph getCCBG(){
		return this.ccbg;
	}
	
	public SootMethod getMethod(){
		return this.method;
	}
	
}
