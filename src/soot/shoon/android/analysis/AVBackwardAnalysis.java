package soot.shoon.android.analysis;

import soot.Unit;
import soot.shoon.android.analysis.entity.AliasValue;

public class AVBackwardAnalysis {
	
	private SinglePathAnalysis spa;
	private AliasValue av;
	private Unit activationUnit;
	
	public AVBackwardAnalysis(SinglePathAnalysis spa, AliasValue av, Unit activationUnit){
		this.spa = spa;
		this.av = av;
		this.activationUnit = activationUnit;
	}
	
	public void startAVBackward(){
		//TODO
	}
}
