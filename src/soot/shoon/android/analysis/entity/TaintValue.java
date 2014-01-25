package soot.shoon.android.analysis.entity;

import java.util.HashSet;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.jimple.InstanceFieldRef;

public class TaintValue {
	/**
	 * x = z.g
     * x.f = tainted
     */
	private Value taintValue; //x.f
	private Unit activationUnit; //x.f = tainted
	private Set<AliasValue> aliases;
	boolean isHeapAssignment = false;
	
	public TaintValue(Unit activationUnit, Value taintValue){
		this.activationUnit = activationUnit;
		this.taintValue = taintValue;
		this.aliases = new HashSet<AliasValue>();
	}
	
	public void setHeapAssignment(boolean b){
		this.isHeapAssignment = b;
	}
	
	public boolean addAlias(AliasValue alias){
		return this.aliases.add(alias);
	}
	
	public Value getTaintValue(){
		return this.taintValue;
	}
	
	public Unit getActivation(){
		return this.activationUnit;
	}
	
	public Set<AliasValue> getAliases(){
		return this.aliases;
	}
	
	public String getFieldName(){
		String result = null;
		if(isHeapAssignment){
			result = ((InstanceFieldRef)taintValue).getFieldRef().name();
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		sb.append(activationUnit.toString());
		sb.append(" aliases:[");
		for(AliasValue av : aliases){
			sb.append(av.getActivationUnit().toString());
			sb.append(", ");
		}
		sb.append("]");
		sb.append("}\n");
		return sb.toString();
	}
	
	
	
}
