package soot.shoon.android.analysis.entity;

import java.util.HashSet;
import java.util.Set;

import soot.SootMethod;

public class SootMethodNode {
	private SootMethod method;
	private SootMethodNode parent;
	private Set<SootMethodNode> sons;
	
	public SootMethodNode(SootMethod method, SootMethodNode parent,
			Set<SootMethodNode> sons) {
		super();
		this.method = method;
		this.parent = parent;
		this.sons = new HashSet<SootMethodNode>();
	}

	public SootMethodNode getParent(){
		return this.parent;
	}
	
	public void addSon(SootMethodNode son){
		if(!this.sons.contains(son)){
			this.sons.add(son);
		}
	}
	
	public SootMethod getMethod(){
		return this.method;
	}
	
	public boolean isMyAncestor(SootMethod method){
		boolean result = false;
	
		SootMethodNode tmpNode = this;
		while(tmpNode != null && !result){
			if(tmpNode.getMethod().getSignature().equals(method.getSignature())){
				result = true;
				break;
			}
			tmpNode = tmpNode.getParent();
		}
		
		return result;
	}
	
}
