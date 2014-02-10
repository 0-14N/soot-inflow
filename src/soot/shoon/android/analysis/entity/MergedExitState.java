package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import soot.jimple.StaticFieldRef;

public class MergedExitState {
	private TaintValue mergedExitThisTV;
	private ArrayList<AliasValue> mergedExitThisAVs;
	private ArrayList<TaintValue> mergedExitArgTVs;
	private ArrayList<ArrayList<AliasValue>> mergedExitArgAVs;
	private ArrayList<StaticFieldRef> staticFieldTVs;
	private HashMap<StaticFieldRef, Set<AliasValue>> staticFieldAVs;
	private TaintValue mergedRetTV;
	private ArrayList<AliasValue> mergedRetAVs;
	
	public MergedExitState(){
		this.mergedExitArgTVs = null;
		this.mergedExitThisAVs = new ArrayList<AliasValue>();
		this.staticFieldTVs = new ArrayList<StaticFieldRef>();
		this.staticFieldAVs = new HashMap<StaticFieldRef, Set<AliasValue>>();
		this.mergedRetTV = null;
		this.mergedRetAVs = new ArrayList<AliasValue>();
	}
	
	
	
	public TaintValue getMergedExitThisTV() {
		return mergedExitThisTV;
	}



	public ArrayList<AliasValue> getMergedExitThisAVs() {
		return mergedExitThisAVs;
	}



	public ArrayList<TaintValue> getMergedExitArgTVs() {
		return mergedExitArgTVs;
	}



	public ArrayList<ArrayList<AliasValue>> getMergedExitArgAVs() {
		return mergedExitArgAVs;
	}



	public ArrayList<StaticFieldRef> getStaticFieldTVs() {
		return staticFieldTVs;
	}
	
	public void addStaticFieldTV(StaticFieldRef sfr){
		if(!this.staticFieldTVs.contains(sfr)){
			this.staticFieldTVs.add(sfr);
		}
	}

	public void addStaticFieldAV(StaticFieldRef sfr, AliasValue av){
		Set<AliasValue> avSet = this.staticFieldAVs.get(sfr);
		if(avSet == null){
			avSet = new HashSet<AliasValue>();
			avSet.add(av);
			this.staticFieldAVs.put(sfr, avSet);
		}else{
			boolean isExisted = false;
			for(AliasValue item : avSet){
				if(item.myEquals(av)){
					isExisted = true;
					break;
				}
			}
			if(!isExisted){
				avSet.add(av);
			}
		}
	}
	
	public void addAllStaticFieldTVs(ArrayList<StaticFieldRef> sfrs){
		for(StaticFieldRef sfr : sfrs){
			if(!this.staticFieldTVs.contains(sfr)){
				this.staticFieldTVs.add(sfr);
			}
		}
	}
	
	public void addAllStaticFieldAVs(HashMap<StaticFieldRef, Set<AliasValue>> sfAVMap){
		Iterator iter = sfAVMap.entrySet().iterator();
		while(iter.hasNext()){
			Entry<StaticFieldRef, Set<AliasValue>> entry = (Entry<StaticFieldRef, Set<AliasValue>>) iter.next();
			StaticFieldRef sfr = entry.getKey();
			Set<AliasValue> avs = entry.getValue();
			for(AliasValue av : avs){
				addStaticFieldAV(sfr, av);
			}
		}
	}

	public HashMap<StaticFieldRef, Set<AliasValue>> getStaticFieldAVs() {
		return staticFieldAVs;
	}

	public TaintValue getMergedRetTV() {
		return mergedRetTV;
	}



	public ArrayList<AliasValue> getMergedRetAVs() {
		return mergedRetAVs;
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
