package soot.shoon.android.analysis.entity;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import soot.SootFieldRef;
import soot.Value;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;
import soot.shoon.android.analysis.SingleMethodAnalysis;
import soot.toolkits.graph.Block;

public class MethodSummary {
	private Map<ArrayList<Block>, PathSummary> pathSummaries;
	
	private SingleMethodAnalysis sma;
	
	private MethodInitState mis;
	
	private MergedExitState mes;
	
	public MethodSummary(SingleMethodAnalysis sma){
		this.pathSummaries = new HashMap<ArrayList<Block>, PathSummary>();
		this.sma = sma;
		this.mis = new MethodInitState(this);
		this.mes = new MergedExitState();
	}
	
	public MethodInitState getMethodInitState(){
		return this.mis;
	}
	
	public void addPathSummary(ArrayList<Block>path, PathSummary ps){
		this.pathSummaries.put(path, ps);
	}
	
	public void mergePathSummaries(){
		//init the merged exit state
		int argsCount = sma.getMethod().getParameterCount();
		this.mes.initExitState(argsCount);
		
		Iterator iter = pathSummaries.entrySet().iterator();
		while(iter.hasNext()){
			PathSummary ps = (PathSummary) ((Entry)iter.next()).getValue();
			Set<TaintValue> tvSet = ps.getTaintsSet();
			Set<AliasValue> avSet = ps.getAliasValues();
			SinglePathExitState spes = ps.getSinglePathExitState();
			TaintValue retTV = ps.getSinglePathExitState().getRetTV();
			ArrayList<AliasValue> retAVs = ps.getSinglePathExitState().getRetAVs();
			
			Iterator<TaintValue> tvIter = tvSet.iterator();
			while(tvIter.hasNext()){
				TaintValue tv = tvIter.next();
				Value v = tv.getTaintValue();
				
				//if this is an instance method, handle 'this' first
				if(!sma.getMethod().isStatic()){
					//rn.t, then produce an alias, base:rn, fieldref:t
					if(v instanceof InstanceFieldRef){
						InstanceFieldRef ifr = (InstanceFieldRef) v;
						Value base = ifr.getBase();
						SootFieldRef sfr = ifr.getFieldRef();
						//this
						if(base.toString().equals("r0")){
							AliasValue newAV = new AliasValue(null, null, base);
							newAV.appendField(sfr);
							this.mes.addExitThisAV(newAV);
						}else{
							int regIndex = Integer.parseInt(base.toString().substring(1));
							if(regIndex > 0 && regIndex <= argsCount){
								AliasValue newAV = new AliasValue(null, null, base);
								newAV.appendField(sfr);
								this.mes.addExitArgAV(regIndex - 1, newAV);
							}
						}
					}else{//rn
						//this
						if(v.toString().equals("r0")){
							TaintValue newTV = new TaintValue(null, v);
							this.mes.setExitThisTV(newTV);
						}else{
							int regIndex = Integer.parseInt(v.toString().substring(1));
							if(regIndex > 0 && regIndex <= argsCount){
								TaintValue newTV = new TaintValue(null, v);
								this.mes.setExitArgTV(regIndex - 1, newTV);
							}
						}
					}
				}else{
					//TODO
					assert(true == false);
				}
			}
			
			Iterator<AliasValue> avIter = avSet.iterator();
			while(avIter.hasNext()){
				AliasValue av = avIter.next();
				Value base = av.getAliasBase();
				ArrayList<SootFieldRef> accessPath = av.getAccessPath();
				
				if(!sma.getMethod().isStatic()){
					//this
					if(base.toString().equals("r0")){
						AliasValue newAV = new AliasValue(null, null, base);
						for(SootFieldRef sfr : accessPath){
							newAV.appendField(sfr);
						}
						this.mes.addExitThisAV(newAV);
					}else{
						int regIndex = Integer.parseInt(base.toString().substring(1));
						if(regIndex > 0 && regIndex <= argsCount){
							AliasValue newAV = new AliasValue(null, null, base);
							for(SootFieldRef sfr : accessPath){
								newAV.appendField(sfr);
							}
							this.mes.addExitArgAV(regIndex, newAV);
						}
					}
				}else{
					//TODO
					assert(true == false);
				}
			}
		}
	}
}