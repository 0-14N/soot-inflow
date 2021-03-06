package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import soot.Body;
import soot.Scene;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CaughtExceptionRef;
import soot.jimple.DefinitionStmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;
import soot.toolkits.graph.ZonedBlockGraph;
import soot.util.Chain;

public class MethodPathCreator {
	private static MethodPathCreator instance;
	
	private MethodPathCreator(){}
	
	public static MethodPathCreator v(){
		if(instance == null){
			instance = new MethodPathCreator();
		}
		return instance;
	}

	/**
	 * get all the paths (sequence of blocks) of a SootMethod from start to end
	 * @param method
	 * @return
	 */
	//public ArrayList<ArrayList<Block>> getPaths(ClassicCompleteBlockGraph graph){
	public ArrayList<ArrayList<Block>> getPaths(ZonedBlockGraph graph){
		ArrayList<ArrayList<Block>> result = new ArrayList<ArrayList<Block>>();
		List<Block> allBlocks = graph.getBlocks();
		List<Block> heads = graph.getHeads();
		List<Block> tails = graph.getTails();
		int i = 0;
	
		/*
		HashMap<Unit, Block> tryCatchUnitMap = new HashMap<Unit, Block>();
		Body body = graph.getBody();
		Chain<Trap> traps = body.getTraps();
		Iterator<Trap> trapIter = traps.iterator();
		while(trapIter.hasNext()){
			Trap trap = trapIter.next();
			Unit tryEnd = trap.getEndUnit();
			Unit handlerBegin = trap.getHandlerUnit();
			for(i = 0; i < heads.size(); i++){
				Block headBlk = heads.get(i);
				Unit headU = headBlk.getHead();
				if(headU.equals(handlerBegin)){
					tryCatchUnitMap.put(tryEnd, headBlk);
				}
			}
		}
		*/
		
		HashMap<String, Block> exceptionHandlers = new HashMap<String, Block>();
		for(i = 0; i < heads.size(); i++){
			Block headBlk = heads.get(i);
			Unit headU = headBlk.getHead();
			if(headU instanceof DefinitionStmt){
				DefinitionStmt ds = (DefinitionStmt) headU;
				Value rv = ds.getRightOp();
				Value lv = ds.getLeftOp();
				if(rv instanceof CaughtExceptionRef){
					String exceptionType = lv.getType().toString();
					exceptionHandlers.put(exceptionType, headBlk);
				}
			}
		}
		
		for(i = 0; i < heads.size(); i++){
			Block head = heads.get(i);
			ArrayList<Integer> source = new ArrayList<Integer>();
			//get the paths start from this head
			ArrayList<ArrayList<Integer>> intLists = forkPaths(source, head, allBlocks, tails);
			//convert the integer list to block list
			for(ArrayList<Integer> intList : intLists){
				ArrayList<Block> blockList = new ArrayList<Block>();
				for(Integer integer : intList){
					Block b = allBlocks.get(integer.intValue());
					blockList.add(b);
					//if the block throws an exception
					Unit tail = b.getTail();
					if(tail instanceof ThrowStmt){
						ThrowStmt ts = (ThrowStmt) tail;
						Value exception = ts.getOp();
						String exceptionType = exception.getType().toString();
						Block handlerBlk = exceptionHandlers.get(exceptionType);
						if(handlerBlk != null){
							blockList.add(handlerBlk);
						}
					}/*else{
						Block handlerBlk = tryCatchUnitMap.get(tail);
						if(handlerBlk != null){
							blockList.add(handlerBlk);
						}
					}
					*/
				}
				result.add(blockList);
			}
		}
		return result;
	}

	/**
	 * a recursive call for expanding the path until we meet a end
	 * @param source : the path before handling the "branch"
	 * @param branch : the block being handled, maybe the "branch" is not a branch (only has one succor)
	 * @param allBlocks : it is used for querying the index of a block
	 * @param tails : it is used for judging whether it comes to end
	 * @return
	 */
	private ArrayList<ArrayList<Integer>> forkPaths(ArrayList<Integer> source, Block branch, List<Block> allBlocks, List<Block> tails){
		ArrayList<ArrayList<Integer>> results = new ArrayList<ArrayList<Integer>>();
		//branch is one of the end blocks
		if(tails.contains(branch)){
			source.add(new Integer(allBlocks.indexOf(branch)));
			results.add(source);
		}else{
			List<Block> succors = branch.getSuccs();
			//branch has only one succor, append to the end of source
			if(succors.size() == 1){
				source.add(new Integer(allBlocks.indexOf(branch)));
				ArrayList<ArrayList<Integer>> tmp = forkPaths(source, succors.get(0), allBlocks, tails);
				results.addAll(tmp);
			}else{//more than one succors, produce a new path for each succor
				int i = 0;
				source.add(new Integer(allBlocks.indexOf(branch)));
				for(; i < succors.size(); i++){
					Block succor = succors.get(i);
					//this is a loop, the succor is already in the previous list
					int loopStart = -1;
					if((loopStart = isInList(source, allBlocks.indexOf(succor))) != -1){
						//add the loop to the source and continue to handle other succors
						int tmpSize = source.size();
						for(int j = loopStart; j < tmpSize; j++){
							source.add(new Integer(source.get(j).intValue()));
						}
						continue;
					}else{
						ArrayList<Integer> clone = cloneList(source);
						ArrayList<ArrayList<Integer>> tmp =  forkPaths(clone, succor, allBlocks, tails);
						results.addAll(tmp);
					}
				}
			}
		}
		return results;
	}
	
	private int isInList(ArrayList<Integer> lst, int n){
		int result = -1;
		for(int i = 0; i < lst.size(); i++){
			if(lst.get(i).intValue() == n){
				result = i;
				break;
			}
		}
		return result;
	}
	
	private ArrayList<Integer> cloneList(ArrayList<Integer> source){
		ArrayList<Integer> result = new ArrayList<Integer>();
		for(int i = 0; i < source.size(); i++){
			Integer integer = new Integer(source.get(i).intValue());
			result.add(integer);
		}
		return result;
	}
	
}
