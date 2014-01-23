package soot.shoon.android.analysis.entity;

import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;

/**
 * @author chenxiong
 *
 */
public class AliasValue {
	/**
	 * x = z.g
     * x.f = tainted
     */
	private Unit activationUnit; //x = z.g
	private TaintValue source; //source.taintValue = "x.f"
	private Value aliasBase; //z.g
	
	public AliasValue(Unit activationUnit, TaintValue source, Value aliasBase){
		this.activationUnit = activationUnit;
		this.source = source;
		this.aliasBase = aliasBase;
		source.addAlias(this);
	}

	public Unit getActivationUnit() {
		return activationUnit;
	}

	public TaintValue getSource() {
		return source;
	}

	public Value getAliasBase() {
		return aliasBase;
	}

	public void setActivationUnit(Unit activationUnit) {
		this.activationUnit = activationUnit;
	}

	public void setSource(TaintValue source) {
		this.source = source;
	}

	public void setAliasBase(Value aliasBase) {
		this.aliasBase = aliasBase;
	}
	
	public boolean isMe(InstanceFieldRef ifr){
		boolean result = false;
		if(ifr.getBase().toString().equals(aliasBase.toString()) && source.getFieldName().equals(ifr.getFieldRef().name())){
			result = true;
		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		sb.append(activationUnit.toString());
		sb.append(", ");
		sb.append(aliasBase.toString());
		sb.append(", ");
		sb.append(source.getActivation().toString());
		sb.append("}\n");
		return sb.toString();
	}
	
}
