package soot.shoon.android.analysis;

import soot.Unit;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.InstanceFieldRef;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.TaintValue;

public class BackwardAnalysis {
	
	private SinglePathAnalysis spa;
	private Unit activationUnit;
	//w.f = t
	private TaintValue tv;//t
	private InstanceFieldRef fr;//w.f
	
	public BackwardAnalysis(Unit activationUnit, TaintValue tv, 
			SinglePathAnalysis spa){
		this.activationUnit = activationUnit;
		this.spa = spa;
		this.tv = tv;
	}
	
	
	public void startBackward(){
		int currIndex = spa.getPathSummary().indexOfUnit(activationUnit);
		while(currIndex >= 0){
			Unit currUnit = spa.getPathSummary().getUnitAt(currIndex);
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
					if(lv.toString().equals(base.toString())){
						AliasValue av = new AliasValue(currUnit, tv, rv);
						spa.getPathSummary().addAlias(av);
						ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, av);
						fa.startForward();
					}else if(rv.toString().equals(base.toString())){
						AliasValue av = new AliasValue(currUnit, tv, lv);
						spa.getPathSummary().addAlias(av);
						ForwardAnalysis fa = new ForwardAnalysis(currUnit, spa, av);
						fa.startForward();
					}
				}
			}
			currIndex--;
		}
	}
}
