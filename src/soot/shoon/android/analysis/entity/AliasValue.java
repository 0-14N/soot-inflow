package soot.shoon.android.analysis.entity;

import java.util.ArrayList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.SootFieldRef;
import soot.Unit;
import soot.Value;
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
	private Value aliasBase; //z
	private ArrayList<SootFieldRef> accessPath;
	private int activationIndex;
	
	public AliasValue(Unit activationUnit, TaintValue source, Value aliasBase){
		this.activationUnit = activationUnit;
		this.source = source;
		this.aliasBase = aliasBase;
		this.accessPath = new ArrayList<SootFieldRef>();
		this.activationIndex = 0;
		
		if(source != null){
			source.addAlias(this);
		}
	}
	
	public void setActivationIndex(int index){
		this.activationIndex = index;
	}
	
	public int getActivationIndex(){
		return this.activationIndex;
	}
	
	public void appendField(SootFieldRef sfr){
		this.accessPath.add(sfr);
	}
	
	public ArrayList<SootFieldRef> getAccessPath(){
		return this.accessPath;
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
	
	public boolean isMe(InstanceFieldRef ifr){
		boolean result = false;
		if(accessPath.size() == 1){
			Value base = ifr.getBase();
			SootFieldRef srf = ifr.getFieldRef();
			if(aliasBase.toString().equals(base.toString()) &&
				srf.toString().equals(accessPath.get(0).toString())){
				result = true;
			}
		}
		return result;
	}
	
	/**
	 * (p0 = p1)
	 * p1 = p0; ———————————————— p1.f******base: p1, source: p0.f = tainted_value
	 * p2.g = p1; ———————————————- p2.g.f******base: p2, accessPath{g, f}
     * p3.h = p2; ———————————————- p3.h.g.f
	 * p4.k = p3; ———————————————- p4.k.h.g.f
	 * t1 = p4.k; ———————————————- t1.h.g.f
	 * t2 = t1.h; ———————————————- t2.g.f
	 * t3 = t2.g; ———————————————- t3.f
	 * t4 = t3.f;
	 * p0.f = tainted_value; ——————————— p0.f is a taint value
	 * t4 = t3.f;
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(aliasBase.toString());
		for(int i = 0; i < accessPath.size(); i++){
			sb.append("@");
			SootFieldRef sfr = accessPath.get(i);
			sb.append(sfr.name());
			sb.append("[");
			sb.append(sfr.type().toString());
			sb.append("]");
		}
		return sb.toString();
	}
	
	/** x = y.s; //y.s.f is an alias
	 * x.f = tainted;
	 * g = y.s; //call isAliasBase(y.s), return true
	 * j = g.f; 
	 * n = y; //n.s.f
	 * sink(j);
	 */
	public boolean isWithinAccessPath(Value value){
		boolean result = false;
		if(value instanceof InstanceFieldRef){
			InstanceFieldRef ifr = (InstanceFieldRef) value;
			if(ifr.getBase().toString().equals(aliasBase.toString())){
				if(accessPath.size() > 0){
					SootFieldRef sfr = ifr.getFieldRef();
					if(accessPath.get(0).toString().equals(sfr.toString())){
						result = true;
					}
				}
			}
		}else{
			if(value.toString().equals(aliasBase.toString())){
				result = true;
			}
		}
		return result;
	}
	
	public boolean myEquals(Object o){
		boolean result = false;
		if(o instanceof AliasValue){
			AliasValue av = (AliasValue) o;
			if(aliasBase.toString().equals(av.getAliasBase().toString())){
				ArrayList<SootFieldRef> fieldRefs = av.getAccessPath();
				if(fieldRefs.size() == this.accessPath.size()){
					int length = this.accessPath.size();
					for(int i = 0; i < length; i++){
						if(!this.accessPath.get(i).toString().equals(fieldRefs.get(i).toString())){
							break;
						}
					}
					result = true;
				}
			}
		}
		return result;
	}
	
}
