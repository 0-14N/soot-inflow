package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;

public class PathSummary {
	private ArrayList<Unit> allUnits;
	private ArrayList<InvokeExpr> invokeExprs;
	private Set<TaintValue> taintsSet;
	private Set<AliasValue> aliasSet;
	//initial MethodSummary
	private MethodSummary initMethodSummary;
	
	public PathSummary(ArrayList<Unit> allUnits){
		this.invokeExprs = new ArrayList<InvokeExpr>();
		this.taintsSet = new HashSet<TaintValue>();
		this.aliasSet = new HashSet<AliasValue>();
		this.allUnits = allUnits;
		this.initMethodSummary = null;
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
	
	public void addAlias(AliasValue av){
		this.aliasSet.add(av);
	}
	
	public void addTaintValue(TaintValue tv){
		this.taintsSet.add(tv);
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
		for(TaintValue tv : taintsSet){
			if(tv == taintValue){
				Set<AliasValue> aliases = tv.getAliases();
				for(AliasValue alias : aliases){
					aliasSet.remove(alias);
				}
				aliases.clear();
				taintsSet.remove(tv);
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
		if(allUnits.indexOf(av.getActivationUnit()) > allUnits.indexOf(tv.getActivation())){
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
		for(AliasValue tmp : aliasSet){
			if(tmp == av){
				aliasSet.remove(tmp);
			}
		}
	}
	
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

	/**
	 * 
	 * @param value
	 * @param currUnit
	 * @return ==
	 */
	public AliasValue isAlias(Value value, Unit currUnit){
		AliasValue result = null;
		if(value instanceof InstanceFieldRef){
			for(AliasValue av : aliasSet){
				Unit activation = av.getSource().getActivation();
				if(av.isMe((InstanceFieldRef)value) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
					result = av;
					break;
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
	public AliasValue isAliasBase(Value value, Unit currUnit){
		AliasValue result = null;
		for(AliasValue av : aliasSet){
			Unit activation = av.getActivationUnit();
			if(allUnits.indexOf(currUnit) > allUnits.indexOf(activation)){
				if(av.isWithinAccessPath(value)){
					result = av;
					break;
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
}
