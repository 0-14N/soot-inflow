package soot.shoon.android.analysis;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Unit;
import soot.shoon.android.analysis.SingleMethodAnalysis.MethodAnalysisType;
import soot.shoon.android.analysis.entity.PathSummary;

public class SinglePathAnalysis {
	private Logger logger = LoggerFactory.getLogger(getClass());
	
	private Unit activationUnit;
	private PathSummary pSummary;
	private MethodAnalysisType mat;
	
	public SinglePathAnalysis(Unit activationUnit, PathSummary pSummary, MethodAnalysisType mat){
		this.activationUnit = activationUnit;
		this.pSummary = pSummary;
		this.mat = mat;
	}
	
	public void start(){
		if(this.mat == MethodAnalysisType.SourceContainer){
			ForwardAnalysis fa = new ForwardAnalysis(activationUnit, this);
			fa.startForward();
		}
	}
	
	public PathSummary getPathSummary(){
		return this.pSummary;
	}
}
