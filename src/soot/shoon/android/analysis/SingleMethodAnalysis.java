package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.Iterator;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.Stmt;
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
	
	
	public enum MethodAnalysisType{
		SourceContainer,
		Callee,
		Caller
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = MethodAnalysisType.SourceContainer;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
	}
	
	public SingleMethodAnalysis(SootMethod method, ClassicCompleteBlockGraph ccbg, Block activationBlock, Unit activationUnit, MethodAnalysisType type){
		this.method = method;
		this.ccbg = ccbg;
		this.activationBlock = activationBlock;
		this.activationUnit = activationUnit;
		this.type = type;
		this.paths = MethodPathCreator.v().getPaths(ccbg);
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
			if(activationUnit instanceof DefinitionStmt){
				ForwardAnalysis fa = new ForwardAnalysis(activationUnit, allUnits);
				fa.startForward();
			}
		}
	}
}