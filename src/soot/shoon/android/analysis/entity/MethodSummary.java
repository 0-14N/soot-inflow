package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import soot.jimple.StaticFieldRef;
import soot.toolkits.graph.Block;

public class MethodSummary {
	private Map<ArrayList<Block>, PathSummary> pathSummaries;

	//initial state
	private List<StaticFieldRef> staticFields;
	
	public MethodSummary(){
		this.pathSummaries = new HashMap<ArrayList<Block>, PathSummary>();
	}
}