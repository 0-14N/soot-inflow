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
	private AliasValue thisAV;
	private TaintValue[] argTVs;
	private AliasValue[] argAVs;
	
	public MethodSummary(){
		this.pathSummaries = new HashMap<ArrayList<Block>, PathSummary>();
		this.staticFields = new ArrayList<StaticFieldRef>();
		this.thisTV = null;
		this.thisAV = null;
		this.argTVs = null;
		this.argAVs = null;
	}
	
	public void initArgs(int argsCount){
		this.argTVs = new TaintValue[argsCount];
		this.argAVs = new AliasValue[argsCount];
	}
	
	public void setArgTaintValue(int index, TaintValue tv){
		this.argTVs[index] = tv;
	}
	
	public TaintValue getArgTaintValue(int index){
		TaintValue result = this.argTVs[index];
		if(null == result || null == result.getActivation())
			result = null;
		return result;
	}
	
	public void setArgAliasValue(int index, AliasValue av){
		this.argAVs[index] = av;
	}
	
	public AliasValue getArgAliasValue(int index){
		AliasValue result = this.argAVs[index];
		if(null == result || result.getActivationUnit() == null)
			result = null;
		return result;
	}
	
	public void setThisTV(TaintValue tv){
		this.thisTV = tv;
	}
	
	public TaintValue getThisTV(){
		return this.thisTV;
	}
	
	public void setThisAV(AliasValue av){
		this.thisAV = av;
	}
	
	public AliasValue getThisAV(){
		return this.thisAV;
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
	
	public TaintValue[] getAargTVs(){
		return this.argTVs;
	}
}