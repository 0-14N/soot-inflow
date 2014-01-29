package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import soot.jimple.StaticFieldRef;
import soot.toolkits.graph.Block;

public class MethodSummary {
	private Map<ArrayList<Block>, PathSummary> pathSummaries;
	
	private MethodInitState mis;
	
	public MethodSummary(){
		this.pathSummaries = new HashMap<ArrayList<Block>, PathSummary>();
		this.mis = new MethodInitState(this);
	}
	
	public MethodInitState getMethodInitState(){
		return this.mis;
	}
	
	public void addPathSummary(ArrayList<Block>path, PathSummary ps){
		this.pathSummaries.put(path, ps);
	}
}