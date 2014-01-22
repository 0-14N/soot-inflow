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
	
	public ForwardAnalysis(Unit activationUnit, ArrayList<Unit> allUnits){
		this.activationUnit = activationUnit;
		this.allUnits = allUnits;
		this.taintsSet = new HashSet<TaintValue>();
		this.aliasSet = new HashSet<AliasValue>();
		this.issm = IntersectionAnalysisManager.v().getISSM();
		this.icfg = IntersectionAnalysisManager.v().getICFG();
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
				if(issm.isSource(s, icfg)){
					foundNewTaint(currUnit, lv);
				}else if(isTainted(rv, currUnit)){//rv is in taintsSet
					//although it is totally the same as "isSource", we don't merge for clear logic
					foundNewTaint(currUnit, lv);
				}else if(rv instanceof InstanceFieldRef){//right value alias must be instance field
					InstanceFieldRef ifr = (InstanceFieldRef) rv;
					if(isAlias(ifr, currUnit)){
						foundNewTaint(currUnit, lv);
					}
				}else{
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
	
	private void foundNewTaint(Unit currUnit, Value lv){
		//first add the left value to taints set
		TaintValue tv = new TaintValue(currUnit, lv);
		taintsSet.add(tv);
		//then, whether the left value is a FieldRef (only instance field can have alias) TODO
		if(lv instanceof InstanceFieldRef){
			tv.setHeapAssignment(true);
			BackwardAnalysis ba = new BackwardAnalysis(currUnit, allUnits, tv);
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
			if(tv.getTaintValue() == value && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
				result = true;
				break;
			}
		}
		return result;
	}
	
	private boolean isAlias(InstanceFieldRef value, Unit currUnit){
		boolean result = false;
		for(AliasValue av : aliasSet){
			Unit activation = av.getSource().getActivation();
			if(av.isMe(value) && allUnits.indexOf(activation) < allUnits.indexOf(currUnit)){
				result = true;
				break;
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
			if(value == av.getAliasBase() && allUnits.indexOf(currUnit) > allUnits.indexOf(activation)){
				result = av;
				break;
			}
		}
		return result;
	}
	
}
