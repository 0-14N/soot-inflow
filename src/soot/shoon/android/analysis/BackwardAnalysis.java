package soot.shoon.android.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import soot.SootField;
import soot.SootFieldRef;
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

public class BackwardAnalysis {
	
	private ISourceSinkManager issm;
	private IInfoflowCFG icfg;
	
	private Unit activationUnit;
	private ArrayList<Unit> allUnits;
	private TaintValue tv;
	
	private Set<TaintValue> taintsSet;
	private Set<AliasValue> aliasSet;
	
	private InstanceFieldRef fr;
	
	public BackwardAnalysis(Unit activationUnit, ArrayList<Unit> allUnits, TaintValue tv){
		this.activationUnit = activationUnit;
		this.allUnits = allUnits;
		this.taintsSet = new HashSet<TaintValue>();
		this.aliasSet = new HashSet<AliasValue>();
		this.issm = IntersectionAnalysisManager.v().getISSM();
		this.icfg = IntersectionAnalysisManager.v().getICFG();
		this.tv = tv;
	}
	
	
	public void startBackward(){
		int currIndex = allUnits.indexOf(activationUnit);
		while(currIndex >= 0){
			Unit currUnit = allUnits.get(currIndex);
			if(currUnit instanceof DefinitionStmt){
				DefinitionStmt s = (DefinitionStmt) currUnit;
				//if this is activation unit, init fieldref and backward
				if(currUnit == activationUnit){
					this.fr = (InstanceFieldRef) s.getLeftOp();
					currIndex--;
					continue;
				}else{
					assert(fr != null);
					Value lv = s.getLeftOp();
					Value rv = s.getRightOp();
					Value base = fr.getBase();
					if(lv == base){
						AliasValue av = new AliasValue(currUnit, tv, rv);
						aliasSet.add(av);
						ForwardAnalysis fa = new ForwardAnalysis(currUnit, allUnits);
						fa.startForward();
					}else if(rv == base){
						AliasValue av = new AliasValue(currUnit, tv, lv);
						aliasSet.add(av);
						ForwardAnalysis fa = new ForwardAnalysis(currUnit, allUnits);
						fa.startForward();
					}
				}
			}
			currIndex--;
		}
	}
}
