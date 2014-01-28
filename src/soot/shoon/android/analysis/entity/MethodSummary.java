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
	private TaintValue thisTV;
	private ArrayList<AliasValue> thisAVs;
	private ArrayList<TaintValue> argTVs;
	private ArrayList<ArrayList<AliasValue>> argAVs;
	
	public MethodSummary(){
		this.pathSummaries = new HashMap<ArrayList<Block>, PathSummary>();
		this.staticFields = new ArrayList<StaticFieldRef>();
		this.thisTV = null;
		this.thisAVs = new ArrayList<AliasValue>();
		this.argTVs = new ArrayList<TaintValue>();
		this.argAVs = new ArrayList<ArrayList<AliasValue>>();
	}
	
	public void initArgs(int argsCount){
		this.argTVs = new ArrayList<TaintValue>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.argTVs.add(null);
		}
		this.argAVs = new ArrayList<ArrayList<AliasValue>>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.argAVs.add(new ArrayList<AliasValue>());
		}
	}
	
	public void setArgTaintValue(int index, TaintValue tv){
		this.argTVs.set(index, tv);
	}
	
	public TaintValue getArgTaintValue(int index){
		TaintValue result = this.argTVs.get(index);
		if(null == result || null == result.getActivation())
			result = null;
		return result;
	}
	
	public void addArgAliasValue(int index, AliasValue av){
		this.argAVs.get(index).add(av);
	}
	
	public ArrayList<AliasValue> getArgAliasValues(int index){
		ArrayList<AliasValue> result = this.argAVs.get(index);
		if(null == result || result.size() == 0)
			result = null;
		return result;
	}
	
	public void setThisTV(TaintValue tv){
		this.thisTV = tv;
	}
	
	public TaintValue getThisTV(){
		return this.thisTV;
	}
	
	public void addThisAV(AliasValue av){
		this.thisAVs.add(av);
	}
	
	public ArrayList<AliasValue> getThisAVs(){
		return this.thisAVs;
	}
	
	public void addStaticFieldRef(StaticFieldRef sfr){
		staticFields.add(sfr);
	}
	
	public List<StaticFieldRef> getStaticFieldRefs(){
		return this.staticFields;
	}
	
	public void addPathSummary(ArrayList<Block>path, PathSummary ps){
		this.pathSummaries.put(path, ps);
	}
	
	public ArrayList<TaintValue> getAargTVs(){
		return this.argTVs;
	}
}