package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.Iterator;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.Unit;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;
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
		this.methodSummary = new MethodSummary();
	}
	
	public SingleMethodAnalysis(SootMethod method, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		this.ccbg = new ClassicCompleteBlockGraph(this.method.getActiveBody());
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(this.ccbg);
		this.methodSummary = new MethodSummary();
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = MethodAnalysisType.SourceContainer;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.methodSummary = new MethodSummary();
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
		this.methodSummary = new MethodSummary();
	}
	
	public MethodSummary getMethodSummary(){
		return this.methodSummary;
	}
	
	public void start(){
		//this method contains a source invoking
		if(this.type == MethodAnalysisType.SourceContainer){
			for(ArrayList<Block> path : paths){
				if(path.contains(activationBlock)){
					analyzeSinglePath(path);
				}
			}
		}
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
			//Set<TaintValue> taintsSet = new HashSet<TaintValue>();
			//Set<AliasValue> aliasSet = new HashSet<AliasValue>();
			//ForwardAnalysis fa = new ForwardAnalysis(activationUnit, allUnits, taintsSet, aliasSet);
			//fa.startForward();
			PathSummary pSummary = new PathSummary(allUnits);
			SinglePathAnalysis spa = new SinglePathAnalysis(this, activationUnit, pSummary, this.type);
			spa.start();
			logger.info("path done!");
		}else if(this.type == MethodAnalysisType.Callee){
			
		}
	}
	
	public ClassicCompleteBlockGraph getCCBG(){
		return this.ccbg;
	}
}
