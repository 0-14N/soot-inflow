package soot.shoon.android.analysis;

import soot.Unit;
import soot.Value;

public class AliasValue {
	Unit activationUnit;
	Value alias;
	Value source;
	
	public Unit getActivationUnit() {
		return activationUnit;
	}
	public Value getAlias() {
		return alias;
	}
	public Value getSource() {
		return source;
	}
	public void setActivationUnit(Unit activationUnit) {
		this.activationUnit = activationUnit;
	}
	public void setAlias(Value alias) {
		this.alias = alias;
	}
	public void setSource(Value source) {
		this.source = source;
	}
	
	
}
