package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.List;

import soot.SootMethod;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;

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
	public ArrayList<ArrayList<Block>> getPaths(ClassicCompleteBlockGraph graph){
		ArrayList<ArrayList<Block>> result = new ArrayList<ArrayList<Block>>();
		List<Block> allBlocks = graph.getBlocks();
		List<Block> heads = graph.getHeads();
		List<Block> tails = graph.getTails();
		
		int i = 0;
		for(; i < heads.size(); i++){
			Block head = heads.get(i);
			ArrayList<Integer> source = new ArrayList<Integer>();
			//get the paths start from this head
			ArrayList<ArrayList<Integer>> intLists = forkPaths(source, head, allBlocks, tails);
			//convert the integer list to block list
			for(ArrayList<Integer> intList : intLists){
				ArrayList<Block> blockList = new ArrayList<Block>();
				for(Integer integer : intList){
					blockList.add(allBlocks.get(integer.intValue()));
				}
				result.add(blockList);
			}
		}
		return result;
	}

	/**
	 * a recursive call for expanding the path until we meet a end
	 * @param source : the path before handling the "branch"
	 * @param branch : the block being handled, maybe the "branch" is not a branch (only one succor)
	 * @param allBlocks : it is used for querying the index of a block
	 * @param tails : it is used for judging whether come to end
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
					if(isInList(source, allBlocks.indexOf(succor))){
						//add the loop to the source and continue to handle other succors
						int loopStart = source.indexOf(succor);
						for(int j = loopStart; j < source.size(); j++){
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
	
	private boolean isInList(ArrayList<Integer> lst, int n){
		boolean result = false;
		for(int i = 0; i < lst.size(); i++){
			if(lst.get(i).intValue() == n){
				result = true;
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
