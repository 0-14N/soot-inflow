package soot.shoon.android.analysis.entity;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;

/**
 * @author chenxiong
 *
 */
public class AliasValue {
	private Logger logger = LoggerFactory.getLogger(getClass());
	/**
	 * x = z.g
     * x.f = tainted
     */
	private Unit activationUnit; //x = z.g
	private TaintValue source; //source.taintValue = "x.f"
	private Value aliasBase; //z.g
	private AliasValue previousAV;//to fix the issue2:https://github.com/0-14N/soot-inflow/issues/2
	
	public AliasValue(Unit activationUnit, TaintValue source, Value aliasBase, AliasValue previousAV){
		this.activationUnit = activationUnit;
		this.source = source;
		this.aliasBase = aliasBase;
		this.previousAV = previousAV;
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
	
	public AliasValue getPreviousAV(){
		return this.previousAV;
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
		/*
		if(ifr.getBase().toString().equals(aliasBase.toString()) && source.getFieldName().equals(ifr.getFieldRef().name())){
			result = true;
		}*/
		//fix issue2
		if(ifr.toString().equals(this.toString())){
			result = true;
		}
		return result;
	}
	
	public int getAccessPathLength(){
		if(this.previousAV == null){
			return 1;
		}else{
			if(aliasBase instanceof FieldRef){
				return 2 + this.previousAV.getAccessPathLength();
			}else{
				return 1 + this.previousAV.getAccessPathLength();
			}
		}
	}

	/**
	 * (p0 = p1)
	 * p1 = p0; ———————————————— p1.f******base: p1, source: p0.f = tainted_value, preAV = null
	 * p2.g = p1; ———————————————- p2.g.f******base: p2.g, preAV —> “p1 = p0"
     * p3.h = p2; ———————————————- p3.h.g.f******base: p3.h, preAV —> “p2.g = p1"
	 * p4.k = p3; ———————————————- p4.k.h.g.f********base: p4.k, preAV —> “p3.h = p2"
	 * t1 = p4.k; ———————————————- t1.h.g.f*********base: t1, preAV —> “p4.k = p3"
	 * t2 = t1.h; ———————————————- t2.g.f*********base: t2, preAV —> “t1 = p4.k"
	 * t3 = t2.g; ———————————————- t3.f*********base: t3, preAV —>”t2 = t1.h"
	 * t4 = t3.f;
	 * p0.f = tainted_value; ——————————— p0.f is a taint value
	 * t4 = t3.f;
	 */
	@Override
	public String toString() {
		//TODO the string format is not right
		if(this.previousAV == null){
			return aliasBase.toString() + "." + source.getFieldName();
		}else{
			assert(activationUnit instanceof DefinitionStmt);
			DefinitionStmt ds = (DefinitionStmt) activationUnit;
			String rvStr = ds.getRightOp().toString();
			return this.aliasBase.toString() + this.previousAV.toString().split(rvStr)[1];//a little bit of trick
		}
	}
	
}
