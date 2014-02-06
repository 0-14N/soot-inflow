package soot.shoon.android.analysis;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Unit;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.MethodSummary;
import soot.shoon.android.analysis.entity.PathSummary;

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
		}else if(this.mat == MethodAnalysisType.Caller){
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
