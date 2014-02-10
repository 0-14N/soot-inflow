package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.List;

import soot.jimple.StaticFieldRef;

public class SinglePathExitState {
		//exit state
		private TaintValue retTV;
		private ArrayList<AliasValue> retAVs;
		
		private PathSummary ps;
		
		public SinglePathExitState(PathSummary ps){
			this.retTV = null;
			this.retAVs = new ArrayList<AliasValue>();
			this.ps = ps;
		}
		
		public TaintValue getRetTV(){
			return this.retTV;
		}
		
		public void setRetTV(TaintValue retTV){
			this.retTV = retTV;
		}
		
		public ArrayList<AliasValue> getRetAVs(){
			return this.retAVs;
		}
		
		public void addRetAV(AliasValue retAV){
			this.retAVs.add(retAV);
		}
		
		public void addAllRetAVs(ArrayList<AliasValue> retAVs){
			this.retAVs.addAll(retAVs);
		}
}
