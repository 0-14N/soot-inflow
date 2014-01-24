package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.TaintValue;

//forward analysis begins when meet a new taint value 
public class ForwardAnalysis {
	
	private ISourceSinkManager issm;
	private IInfoflowCFG icfg;
	
	private Unit activationUnit;
	private ArrayList<Unit> allUnits;
	
	private Set<TaintValue> taintsSet;
	private Set<AliasValue> aliasSet;
	
	private AliasValue currAliasValue;
	
	//this is used for the first ForwardAnalysis
	public ForwardAnalysis(Unit activationUnit, ArrayList<Unit> allUnits, 
			Set<TaintValue> taintsSet, Set<AliasValue> aliasSet){
		this.activationUnit = activationUnit;
		this.allUnits = allUnits;
		assert(taintsSet != null && aliasSet != null);
		this.taintsSet = taintsSet;
		this.aliasSet = aliasSet;
		this.issm = IntersectionAnalysisManager.v().getISSM();
		this.icfg = IntersectionAnalysisManager.v().getICFG();
		this.currAliasValue = null;
	}
	
	//this is used when found an alias
	public ForwardAnalysis(Unit activationUnit, ArrayList<Unit> allUnits, 
			Set<TaintValue> taintsSet, Set<AliasValue> aliasSet, AliasValue av){
		this.activationUnit = activationUnit;
		this.allUnits = allUnits;
		assert(taintsSet != null && aliasSet != null);
		this.taintsSet = taintsSet;
		this.aliasSet = aliasSet;
		this.issm = IntersectionAnalysisManager.v().getISSM();
		this.icfg = IntersectionAnalysisManager.v().getICFG();
		this.currAliasValue = av;
	}
	
	public void startForward(){
		int currIndex = allUnits.indexOf(activationUnit);
		int length = allUnits.size();
		while(currIndex < length){
			Unit currUnit = allUnits.get(currIndex);
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				Value lv = s.getLeftOp();
				Value rv = s.getRightOp();
					//if this a source
					if(currAliasValue == null && issm.isSource(s, icfg)){
						foundNewTaint(currUnit, lv);
					}else if(isTainted(rv, currUnit)){//rv is in taintsSet
						foundNewTaint(currUnit, lv);
					}else if(isAlias(rv, currUnit)){
						foundNewTaint(currUnit, lv);
					}else{// the right value is not tainted
						//if the left value is already tainted
						if(isTainted(lv, currUnit)){
							deleteTaint(lv, currUnit);
						}else if(isAlias(lv, currUnit)){//if the left value is an alias
							deleteAlias(lv, currUnit);
						}
						//if the right value is an alias's base, produce a new alias
						AliasValue tmp;
						if((tmp = isAliasBase(rv, currUnit)) != null){
							AliasValue av = new AliasValue(currUnit, tmp.getSource(), lv);
							aliasSet.add(av);
						}
					}
			}
			currIndex++;
		}
	}
	
	private void deleteTaint(Value lv, Unit currUnit){
		for(TaintValue tv : taintsSet){
			Value value = tv.getTaintValue();
			if(lv.toString().equals(value.toString()) && 
					allUnits.indexOf(currUnit) > allUnits.indexOf(tv.getActivation())){
				Set<AliasValue> aliases = tv.getAliases();
				for(AliasValue alias : aliases){
					aliasSet.remove(alias);
				}
				aliases.clear();
				taintsSet.remove(tv);
			}
		}
	}
	
	private void deleteAlias(Value lv, Unit currUnit){
		assert(lv instanceof InstanceFieldRef);
		InstanceFieldRef ifr = (InstanceFieldRef) lv;
		for(AliasValue av : aliasSet){
			if(av.isMe(ifr) && allUnits.indexOf(currUnit) > allUnits.indexOf(av.getActivationUnit())){
				aliasSet.remove(av);
			}
		}
	}

	
	private boolean alreadyInTaintsSet(Unit currUnit, Value lv){
		boolean result = false;
		for(TaintValue tv : taintsSet){
			if(tv.getActivation() == currUnit){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private void foundNewTaint(Unit currUnit, Value lv){
		if(alreadyInTaintsSet(currUnit, lv)){
			return;
		}
		//first add the left value to taints set
		TaintValue tv = new TaintValue(currUnit, lv);
		taintsSet.add(tv);
		//then, whether the left value is a FieldRef (only instance field can have alias) TODO
		if(lv instanceof InstanceFieldRef){
			tv.setHeapAssignment(true);
			BackwardAnalysis ba = new BackwardAnalysis(currUnit, allUnits, tv, taintsSet, aliasSet);
			ba.startBackward();
		}
	}

	/**
	 * 
	 * @param value
	 * @param currUnit currUnit must be after the TaintValue's activation
	 * @return
	 */
	private boolean isTainted(Value value, Unit currUnit){
		boolean result = false;
		for(TaintValue tv : taintsSet){
			Unit activation = tv.getActivation();
			Value tmp = tv.getTaintValue();
			if(tmp.toString().equals(value.toString()) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private boolean isAlias(Value value, Unit currUnit){
		boolean result = false;
		if(value instanceof InstanceFieldRef){
			for(AliasValue av : aliasSet){
				Unit activation = av.getSource().getActivation();
				if(av.isMe((InstanceFieldRef)value) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
					result = true;
					break;
				}
			}
		}
		return result;
	}

	/**
	 * x = y.s; //produced a new AliasValue, aliasBase = y.s
	 * x.f = tainted;
	 * g = y.s; //call isAliasBase(y.s), return true
	 * j = g.f; 
	 * sink(j);
	 * @param value
	 * @return
	 */
	private AliasValue isAliasBase(Value value, Unit currUnit){
		AliasValue result = null;
		for(AliasValue av : aliasSet){
			Unit activation = av.getActivationUnit();
			if(value.toString().equals(av.getAliasBase().toString()) && allUnits.indexOf(currUnit) > allUnits.indexOf(activation)){
				result = av;
				break;
			}
		}
		return result;
	}
	
}
