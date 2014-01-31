package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.List;

import soot.jimple.StaticFieldRef;

public class MergedExitState {
	private TaintValue mergedExitThisTV;
	private ArrayList<AliasValue> mergedExitThisAVs;
	private ArrayList<TaintValue> mergedExitArgTVs;
	private ArrayList<ArrayList<AliasValue>> mergedExitArgAVs;
	private List<StaticFieldRef> staticFields;
	private TaintValue mergedRetTV;
	private ArrayList<AliasValue> mergedRetAVs;
	
	public MergedExitState(){
		this.mergedExitArgTVs = null;
		this.mergedExitThisAVs = new ArrayList<AliasValue>();
		this.staticFields = new ArrayList<StaticFieldRef>();
		this.mergedRetTV = null;
		this.mergedRetAVs = new ArrayList<AliasValue>();
	}
	
	public void initExitState(int argsCount){
		this.mergedExitArgTVs = new ArrayList<TaintValue>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.mergedExitArgTVs.add(null);
		}
		
		this.mergedExitArgAVs = new ArrayList<ArrayList<AliasValue>>(argsCount);
		for(int i = 0; i < argsCount; i++){
			this.mergedExitArgAVs.add(new ArrayList<AliasValue>());
		}
	}
	
	public void addExitThisAV(AliasValue av){
		if(!isInExitThisAVs(av)){
			this.mergedExitThisAVs.add(av);
		}
	}
	
	public void setExitThisTV(TaintValue tv){
		this.mergedExitThisTV = tv;
	}
	
	public void addExitArgAV(int index, AliasValue av){
		if(!isInExitArgAVs(index, av)){
			this.mergedExitArgAVs.get(index).add(av);
		}
	}
	
	public void setExitArgTV(int index, TaintValue tv){
		this.mergedExitArgTVs.set(index, tv);
	}
	
	public void setRetTV(TaintValue tv){
		this.mergedRetTV = tv;
	}
	
	public void addRetAV(AliasValue av){
		if(!isInExitRetAVs(av)){
			this.mergedRetAVs.add(av);
		}
	}

	private boolean isInExitArgAVs(int argIndex, AliasValue av){
		boolean result = false;
		ArrayList<AliasValue> aliases = this.mergedExitArgAVs.get(argIndex);
		for(AliasValue tmp : aliases){
			if(tmp.myEquals(av)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private boolean isInExitThisAVs(AliasValue av){
		boolean result = false;
		for(AliasValue tmp : this.mergedExitThisAVs){
			if(tmp.myEquals(av)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private boolean isInExitRetAVs(AliasValue av){
		boolean result = false;
		for(AliasValue tmp : this.mergedRetAVs){
			if(tmp.myEquals(av)){
				result = true;
				break;
			}
		}
		return result;
	}
}
