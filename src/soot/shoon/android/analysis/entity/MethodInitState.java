package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import soot.jimple.StaticFieldRef;

public class MethodInitState {
	//initial state
	private ArrayList<StaticFieldRef> staticFieldTVs;
	private HashMap<StaticFieldRef, Set<AliasValue>> staticFieldAVs;
	private TaintValue thisTV;
	private ArrayList<AliasValue> thisAVs;
	private ArrayList<TaintValue> argTVs;
	private ArrayList<ArrayList<AliasValue>> argAVs;	
	
	private MethodSummary ms;
	
	public MethodInitState(MethodSummary ms){
		this.staticFieldTVs = new ArrayList<StaticFieldRef>();
		this.staticFieldAVs = new HashMap<StaticFieldRef, Set<AliasValue>>();
		this.thisTV = null;
		this.thisAVs = new ArrayList<AliasValue>();
		this.argTVs = new ArrayList<TaintValue>();
		this.argAVs = new ArrayList<ArrayList<AliasValue>>();
		this.ms = ms;
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
		this.staticFieldTVs.add(sfr);
	}
	
	public ArrayList<TaintValue> getAargTVs(){
		return this.argTVs;
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
}
