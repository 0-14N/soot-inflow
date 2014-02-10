package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticFieldRef;

public class PathSummary {
	private ArrayList<Unit> allUnits;
	private ArrayList<InvokeExpr> invokeExprs;
	private Set<TaintValue> taintsSet;
	private Set<AliasValue> aliasSet;
	private ArrayList<StaticFieldRef> staticFieldTVs;
	private HashMap<StaticFieldRef, Set<AliasValue>> staticFieldAVs;
	//initial MethodSummary
	private MethodSummary initMethodSummary;
	
	private SinglePathExitState spes;
	
	public PathSummary(ArrayList<Unit> allUnits){
		this.invokeExprs = new ArrayList<InvokeExpr>();
		this.taintsSet = new HashSet<TaintValue>();
		this.aliasSet = new HashSet<AliasValue>();
		this.allUnits = allUnits;
		this.initMethodSummary = null;
		this.spes = new SinglePathExitState(this);
		this.staticFieldTVs = new ArrayList<StaticFieldRef>();
		this.staticFieldAVs = new HashMap<StaticFieldRef, Set<AliasValue>>();
	}
	
	public void setInitMethodSummary(MethodSummary ms){
		this.initMethodSummary = ms;
	}
	
	public MethodSummary getInitMethodSummary(){
		return this.initMethodSummary;
	}

	public Unit getUnitAt(int index){
		return allUnits.get(index);
	}
	
	public int indexOfUnit(Unit u){
		return allUnits.indexOf(u);
	}
	
	public int getPathLength(){
		return allUnits.size();
	}
	
	public SinglePathExitState getSinglePathExitState(){
		return this.spes;
	}
	
	public void addAlias(AliasValue aliasValue){
		if(!isInAliasSet(aliasValue)){
			this.aliasSet.add(aliasValue);
		}
	}
	
	public void addTaintValue(TaintValue tv){
		if(!isInTaintSet(tv)){
			this.taintsSet.add(tv);
		}
	}
	
	public boolean invokeExparHandled(InvokeExpr ie){
		return invokeExprs.contains(ie);
	}
	
	public void handledInvokeExpr(InvokeExpr ie){
		invokeExprs.add(ie);
	}

	/**
	 * 
	 * @param lv
	 * @param currUnit
	 * @return ==
	 */
	public void deleteTaint(TaintValue taintValue){
		Iterator<TaintValue> iter = taintsSet.iterator();
		while(iter.hasNext()){
			TaintValue tv = iter.next();
			if(tv == taintValue){
				Set<AliasValue> aliases = tv.getAliases();
				for(AliasValue alias : aliases){
					aliasSet.remove(alias);
				}
				aliases.clear();
				iter.remove();
			}
		}
	}

	/**
	 * 
	 * @param av
	 * @return ==
	 */
	public void deleteAlias(AliasValue av){
		//currUnit is after the source(TaintValue)'s activation, delete it
		/**
		 * x = w; 
		 * w.f = tainted;
		 * x.f = null;
		 */
		TaintValue tv = av.getSource();
		int activationIndex = 0;
		if(tv == null){
			activationIndex = av.getActivationIndex();
		}else{
			activationIndex = allUnits.indexOf(tv.getActivation());
		}
		if(allUnits.indexOf(av.getActivationUnit()) > activationIndex){
			deleteTaint(tv);
		}
		//if certain taintvalue is tainted by this alias
		/**
		 * x = w;
		 * w.f = tainted;
		 * g = x.f;
		 * x.f = null;
		 */
		for(TaintValue tmp : taintsSet){
			Value rv = ((DefinitionStmt)tmp.getActivation()).getRightOp();
			if(rv instanceof InstanceFieldRef){
				if(av.isMe((InstanceFieldRef)rv)){
					deleteTaint(tmp);
				}
			}
		}
		
		Iterator<AliasValue> iter = aliasSet.iterator();
		while(iter.hasNext()){
			AliasValue tmp = iter.next();
			iter.remove();
		}
	}
	
	private boolean isInTaintSet(TaintValue newTV){
		boolean result = false;
		for(TaintValue tv : taintsSet){
			if(tv.myEquals(newTV)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private boolean isInAliasSet(AliasValue newAV){
		boolean result = false;
		for(AliasValue av : aliasSet){
			if(av.myEquals(newAV)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	//this method is used to judge whether the statement (which produces taints) has been analyzed
	public boolean alreadyInTaintsSet(Unit currUnit, Value lv){
		boolean result = false;
		for(TaintValue tv : taintsSet){
			if(tv.getActivation() == currUnit){
				result = true;
				break;
			}
		}
		return result;
	}
	
	/**
	 * 
	 * @param value
	 * @param currUnit currUnit must be after the TaintValue's activation
	 * @return ==
	 */
	public TaintValue isTainted(Value value, Unit currUnit){
		TaintValue result = null;
		for(TaintValue tv : taintsSet){
			Unit activation = tv.getActivation();
			Value tmp = tv.getTaintValue();
			if(tmp.toString().equals(value.toString()) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
				result = tv;
				break;
			}
		}
		return result;
	}
	
	public StaticFieldRef isStaticFieldTainted(StaticFieldRef sfr){
		StaticFieldRef result = null;
		for(StaticFieldRef item : this.staticFieldTVs){
			if(item.toString().equals(sfr.toString())){
				result = item;
				break;
			}
		}
		return result;
	}
	
	public Set<AliasValue> getStaticFieldAVs(StaticFieldRef sfr){
		Set<AliasValue> result = null;
		Iterator iter = this.staticFieldAVs.entrySet().iterator();
		while(iter.hasNext()){
			Entry<StaticFieldRef, Set<AliasValue>> entry = (Entry<StaticFieldRef, Set<AliasValue>>) iter.next();
			StaticFieldRef key = entry.getKey();
			Set<AliasValue> avSet = entry.getValue();
			if(key.toString().equals(sfr.toString())){
				result = avSet;
				break;
			}
		}
		return result;
	}

	/**
	 * 
	 * @param value
	 * @param currUnit
	 * @return ==
	 */
	public Set<AliasValue> isAlias(Value value, Unit currUnit){
		Set<AliasValue> result = new HashSet<AliasValue>();
		if(value instanceof InstanceFieldRef){
			for(AliasValue av : aliasSet){
				TaintValue tv = av.getSource();
				int activationIndex = 0;
				if(tv == null){
					activationIndex = av.getActivationIndex();
				}else{
					activationIndex = allUnits.indexOf(tv.getActivation());
				}
				if(av.isMe((InstanceFieldRef)value) && activationIndex < allUnits.indexOf(currUnit)){
					result.add(av);
				}
			}
		}
		return result;
	}
	
	/**
	 * x = y.s; //y.s.f is an alias
	 * x.f = tainted;
	 * g = y.s; //call isAliasBase(y.s), return true
	 * j = g.f; 
	 * sink(j);
	 * @param value
	 * @return ==
	 */
	public Set<AliasValue> isAliasBase(Value value, Unit currUnit){
		Set<AliasValue> result = new HashSet<AliasValue>();
		for(AliasValue av : aliasSet){
			Unit activation = av.getActivationUnit();
			if(allUnits.indexOf(currUnit) > allUnits.indexOf(activation)){
				if(av.isWithinAccessPath(value)){
					result.add(av);
				}
			}
		}
		return result;
	}

	/**
	 * p0.f = tainted_value; ——————————— p0.f is tainted
	 * p1 = p0; ————————————————- p1.f is an alias ********************bug issue3
	 * sink(p1.f); ————————————————   
	 * @param value
	 * @param currUnit
	 * @return
	 */
	public TaintValue isTaintBase(Value value, Unit currUnit){
		TaintValue result = null;
		for(TaintValue tv : taintsSet){
			if(tv.isHeapAssignment){
				InstanceFieldRef ifr = (InstanceFieldRef) tv.getTaintValue();
				if(value.toString().equals(ifr.getBase().toString())
						&& allUnits.indexOf(currUnit) > allUnits.indexOf(tv.getActivation())){
					result = tv;
					break;
				}
			}
		}
		return result;
	}
	
	public Set<TaintValue> getTaintsSet(){
		return this.taintsSet;
	}
	
	public Set<AliasValue> getAliasValues(){
		return this.aliasSet;
	}
	
	public ArrayList<AliasValue> getAllAliases(Value base, Unit currUnit){
		ArrayList<AliasValue> result = new ArrayList<AliasValue>();
		for(AliasValue av : aliasSet){
			int activationIndex = 0;
			if(av.getActivationUnit() == null){
				activationIndex = av.getActivationIndex();
			}else{
				activationIndex = allUnits.indexOf(av.getActivationUnit());
			}
			if(av.isWithinAccessPath(base) &&
					allUnits.indexOf(currUnit) > activationIndex){
				result.add(av);
			}
		}
		return result;
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
	
	public ArrayList<StaticFieldRef> getStaticFieldTVs() {
		return staticFieldTVs;
	}

	public HashMap<StaticFieldRef, Set<AliasValue>> getStaticFieldAVs() {
		return staticFieldAVs;
	}

	private void addStaticFieldAV(StaticFieldRef sfr, AliasValue av){
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
	
}
