package soot.shoon.android.analysis;

import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Unit;
import soot.Value;
import soot.jimple.InstanceFieldRef;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.AliasValue;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;
import soot.shoon.android.analysis.entity.TaintValue;

public class SinglePathAnalysis {
	private Logger logger = LoggerFactory.getLogger(getClass());

	private SingleMethodAnalysis sma;
	private Unit activationUnit;
	private PathSummary pSummary;
	private MethodAnalysisType mat;
	
	public SinglePathAnalysis(SingleMethodAnalysis sma, Unit activationUnit, PathSummary pSummary, MethodAnalysisType mat){
		this.sma = sma;
		this.activationUnit = activationUnit;
		this.pSummary = pSummary;
		this.mat = mat;
	}
	
	public void start(){
		if(this.mat == MethodAnalysisType.SourceContainer){
			ForwardAnalysis fa = new ForwardAnalysis(activationUnit, this);
			fa.startForward();
		}else if(this.mat == MethodAnalysisType.Callee){
			ForwardAnalysis fa = new ForwardAnalysis(activationUnit, this);
			fa.startForward();
		}else if(this.mat == MethodAnalysisType.Caller || this.mat == MethodAnalysisType.DummyMain){
			//when return back from callee, if there are any alias like X.Y, should do backward analysis first
			Set<AliasValue> aliasSet = this.pSummary.getAliasValues();
			Set<TaintValue> taintsSet = this.pSummary.getTaintsSet();
			
			for(TaintValue tv : taintsSet){
				Value v = tv.getTaintValue();
				if(v instanceof InstanceFieldRef){
					tv.setHeapAssignment(true);
					BackwardAnalysis ba = new BackwardAnalysis(activationUnit, tv, this);
					ba.startBackward();
				}
			}
			
			for(AliasValue av : aliasSet){
				AVBackwardAnalysis avba = new AVBackwardAnalysis(this, av, activationUnit);
				avba.startAVBackward();
			}
			
			ForwardAnalysis fa = new ForwardAnalysis(activationUnit, this);
			fa.startForward();
		}
	}

	public SingleMethodAnalysis getSMA(){
		return this.sma;
	}
	
	public PathSummary getPathSummary(){
		return this.pSummary;
	}
	
	public MethodAnalysisType getMethodAnalysisType(){
		return this.mat;
	}
	
}
