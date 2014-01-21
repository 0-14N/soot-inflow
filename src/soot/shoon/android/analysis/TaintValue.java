package soot.shoon.android.analysis;

import soot.Unit;
import soot.Value;

public class TaintValue {
	private Value taintValue;
	private Unit activationUnit;
	
	public TaintValue(Value tV, Unit aU){
		this.taintValue = tV;
		this.activationUnit = aU;
	}

	public Value getTaintValue() {
		return taintValue;
	}

	public Unit getActivationUnit() {
		return activationUnit;
	}

	public void setTaintValue(Value taintValue) {
		this.taintValue = taintValue;
	}

	public void setActivationUnit(Unit activationUnit) {
		this.activationUnit = activationUnit;
	}
	
}
