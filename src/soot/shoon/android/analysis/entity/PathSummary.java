package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;

public class PathSummary {
	private ArrayList<Unit> allUnits;
	private ArrayList<InvokeExpr> invokeExprs;
	private Set<TaintValue> taintsSet;
	private Set<AliasValue> aliasSet;
	
	public PathSummary(ArrayList<Unit> allUnits){
		this.invokeExprs = new ArrayList<InvokeExpr>();
		this.taintsSet = new HashSet<TaintValue>();
		this.aliasSet = new HashSet<AliasValue>();
		this.allUnits = allUnits;
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
	
	public void deleteTaint(Value lv, Unit currUnit){
		for(TaintValue tv : taintsSet){
			Value value = tv.getTaintValue();
			if(lv.toString().equals(value.toString()) && 
					allUnits.indexOf(currUnit) > allUnits.indexOf(tv.getActivation())){
				Set<AliasValue> aliases = tv.getAliases();
				for(AliasValue alias : aliases){
					aliasSet.remove(alias);
				}
				aliases.clear();
				taintsSet.remove(tv);
			}
		}
	}
	
	public void deleteAlias(Value lv, Unit currUnit){
		assert(lv instanceof InstanceFieldRef);
		InstanceFieldRef ifr = (InstanceFieldRef) lv;
		for(AliasValue av : aliasSet){
			if(av.isMe(ifr) && allUnits.indexOf(currUnit) > allUnits.indexOf(av.getActivationUnit())){
				aliasSet.remove(av);
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
	 * @return
	 */
	public boolean isTainted(Value value, Unit currUnit){
		boolean result = false;
		for(TaintValue tv : taintsSet){
			Unit activation = tv.getActivation();
			Value tmp = tv.getTaintValue();
			if(tmp.toString().equals(value.toString()) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	public boolean isAlias(Value value, Unit currUnit){
		boolean result = false;
		if(value instanceof InstanceFieldRef){
			for(AliasValue av : aliasSet){
				Unit activation = av.getSource().getActivation();
				if(av.isMe((InstanceFieldRef)value) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
					result = true;
					break;
				}
			}
		}
		return result;
	}
	
	/**
	 * x = y.s; //produced a new AliasValue, aliasBase = y.s
	 * x.f = tainted;
	 * g = y.s; //call isAliasBase(y.s), return true
	 * j = g.f; 
	 * sink(j);
	 * @param value
	 * @return
	 */
	public AliasValue isAliasBase(Value value, Unit currUnit){
		AliasValue result = null;
		for(AliasValue av : aliasSet){
			Unit activation = av.getActivationUnit();
			if(value.toString().equals(av.getAliasBase().toString()) && allUnits.indexOf(currUnit) > allUnits.indexOf(activation)){
				result = av;
				break;
			}
		}
		return result;
	}
}
