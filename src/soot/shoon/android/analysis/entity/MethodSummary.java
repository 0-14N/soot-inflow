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
	
	public MergedExitState getMergedExitState(){
		return this.mes;
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
			TaintValue retTV = ps.getSinglePathExitState().getRetTV();
			ArrayList<AliasValue> retAVs = ps.getSinglePathExitState().getRetAVs();
			//static fields' tvs and avs
			ArrayList<StaticFieldRef> sfrTVs = ps.getStaticFieldTVs();
			HashMap<StaticFieldRef, Set<AliasValue>> sfrAVs = ps.getStaticFieldAVs();
			
			//add the static fields' taint values and alias values
			this.mes.addAllStaticFieldTVs(sfrTVs);
			this.mes.addAllStaticFieldAVs(sfrAVs);
		
			//taint values
			Iterator<TaintValue> tvIter = tvSet.iterator();
			while(tvIter.hasNext()){
				TaintValue tv = tvIter.next();
				Value v = tv.getTaintValue();
			
				//new produced static field ref
				if(v instanceof StaticFieldRef){
					StaticFieldRef sfr = (StaticFieldRef) v;
					this.mes.addStaticFieldTV(sfr);
				}
				
				//rn.t, then produce an alias, base:rn, fieldref:t
				if(v instanceof InstanceFieldRef){
					InstanceFieldRef ifr = (InstanceFieldRef) v;
					Value base = ifr.getBase();
					SootFieldRef sfr = ifr.getFieldRef();
					//this
					if(base.toString().equals("$r0")){
						AliasValue newAV = new AliasValue(null, null, base);
						newAV.appendField(sfr);
						//'this'
						if(!this.sma.getMethod().isStatic()){
							this.mes.addExitThisAV(newAV);
						}else{
							this.mes.addExitArgAV(0, newAV);
						}
					}else{
						try{
							int regIndex = Integer.parseInt(base.toString().substring(2));
							if(regIndex > 0 && regIndex <= argsCount){
								AliasValue newAV = new AliasValue(null, null, base);
								newAV.appendField(sfr);
								if(!this.sma.getMethod().isStatic()){
									this.mes.addExitArgAV(regIndex - 1, newAV);
								}else{
									this.mes.addExitArgAV(regIndex, newAV);
								}
							}
						}catch(NumberFormatException nfe){
							continue;
						}
					}
				}else{//rn
					//this
					if(v.toString().equals("$r0")){
						TaintValue newTV = new TaintValue(null, v);
						if(!this.sma.getMethod().isStatic()){
							this.mes.setExitThisTV(newTV);
						}else{
							this.mes.setExitArgTV(0, newTV);
						}
					}else{
						try{
							int regIndex = Integer.parseInt(v.toString().substring(2));
							if(regIndex > 0 && regIndex <= argsCount){
								TaintValue newTV = new TaintValue(null, v);
								if(!this.sma.getMethod().isStatic()){
									this.mes.setExitArgTV(regIndex - 1, newTV);
								}else{
									this.mes.setExitArgTV(regIndex, newTV);
								}
							}
						}catch(NumberFormatException nfe){
							continue;
						}
					}
				}
					
			}
		
			//alias values
			Iterator<AliasValue> avIter = avSet.iterator();
			while(avIter.hasNext()){
				AliasValue av = avIter.next();
				Value base = av.getAliasBase();
				ArrayList<SootFieldRef> accessPath = av.getAccessPath();
			
				//new produced static field ref alias
				if(base instanceof StaticFieldRef){
					StaticFieldRef sfr = (StaticFieldRef) base;
					this.mes.addStaticFieldAV(sfr, av);
				}
				
				//this
				if(base.toString().equals("$r0")){
					AliasValue newAV = new AliasValue(null, null, base);
					for(SootFieldRef sfr : accessPath){
						newAV.appendField(sfr);
					}
					if(!this.sma.getMethod().isStatic()){
						this.mes.addExitThisAV(newAV);
					}else{
						this.mes.addExitArgAV(0, newAV);
					}
				}else{
					try{
						int regIndex = Integer.parseInt(base.toString().substring(2));
						if(regIndex > 0 && regIndex <= argsCount){
							AliasValue newAV = new AliasValue(null, null, base);
							for(SootFieldRef sfr : accessPath){
								newAV.appendField(sfr);
							}
							if(!this.sma.getMethod().isStatic()){
								this.mes.addExitArgAV(regIndex - 1, newAV);
							}else{
								this.mes.addExitArgAV(regIndex, newAV);
							}
						}
					}catch(NumberFormatException nfe){
						continue;
					}
				}
			}
			
			//return taint value
			if(retTV != null){
				if(retTV instanceof InstanceFieldRef){
					InstanceFieldRef ifr = (InstanceFieldRef) retTV;
					Value base = ifr.getBase();
					SootFieldRef sfr = ifr.getFieldRef();
					AliasValue newAV = new AliasValue(null, null, base);
					newAV.appendField(sfr);
					this.mes.addRetAV(newAV);
				}else{
					TaintValue newTV = new TaintValue(null, retTV.getTaintValue());
					this.mes.setRetTV(newTV);
				}
			}
			
			//return alias values
			for(AliasValue retAV : retAVs){
				Value base = retAV.getAliasBase();
				ArrayList<SootFieldRef> accessPath = retAV.getAccessPath();
				AliasValue newAV = new AliasValue(null, null, base);
				for(SootFieldRef sfr : accessPath){
					newAV.appendField(sfr);
				}
				this.mes.addRetAV(newAV);
			}
		}
	}
}