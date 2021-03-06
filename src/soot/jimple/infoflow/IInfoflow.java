/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow;

import java.util.List;

import soot.Transform;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
/**
 * interface for the main infoflow class
 *
 */
public interface IInfoflow {
	
	/**
	 * Enumeration containing the callgraph algorithms supported for the use with
	 * the data flow tracker
	 */
	public enum CallgraphAlgorithm {
		AutomaticSelection,
		VTA,
		RTA
	}
	
	/**
	 * Enumeration containing the aliasing algorithms supported by FlowDroid
	 */
	public enum AliasingAlgorithm {
		/**
		 * A fully flow-sensitive algorithm based on Andromeda
		 */
		FlowSensitive,
		/**
		 * A flow-insensitive algorithm based on Soot's point-to-sets
		 */
		PtsBased
	}

	/**
	 * Sets the taint wrapper for deciding on taint propagation through black-box
	 * methods
	 * @param wrapper The taint wrapper object that decides on how information is
	 * propagated through black-box methods
	 */
	public void setTaintWrapper(ITaintPropagationWrapper wrapper);

	/**
	 * Sets whether the information flow analysis shall stop after the first
	 * flow has been found
	 * @param stopAfterFirstFlow True if the analysis shall stop after the
	 * first flow has been found, otherwise false.
	 */
	public void setStopAfterFirstFlow(boolean stopAfterFirstFlow);
	
    /**
     * List of preprocessors that need to be executed in order before
     * the information flow.
     * @param preprocessors the pre-processors
     */
    public void setPreProcessors(List<Transform> preprocessors);

	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPointCreator the entry point creator to use for generating the dummy
	 * main method
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, List<String> sources, List<String> sinks);
	
	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, List<String> entryPoints, List<String> sources,
			List<String> sinks);

	/**
	 * Computes the information flow on a single method. This method is
	 * directly taken as the entry point into the program, even if it is an
	 * instance method.
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoint the main method to analyze
	 * @param sources list of source class+method (as string conforms to SootMethod representation)
	 * @param sinks list of sink class+method (as string conforms to SootMethod representation)
	 */
	public void computeInfoflow(String path, String entryPoint, List<String> sources, List<String> sinks);

	/**
	 * Computes the information flow on a list of entry point methods. This list
	 * is used to construct an artificial main method following the Android
	 * life cycle for all methods that are detected to be part of Android's
	 * application infrastructure (e.g. android.app.Activity.onCreate)
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPointCreator the entry point creator to use for generating the dummy
	 * main method
	 * @param entryPoints the entryPoints (string conforms to SootMethod representation)
	 * @param sourcesSinks manager class for identifying sources and sinks in the source code
	 */
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, ISourceSinkManager sourcesSinks);

	/**
	 * Computes the information flow on a single method. This method is
	 * directly taken as the entry point into the program, even if it is an
	 * instance method.
	 * @param path the path to the main folder of the (unpacked) class files
	 * @param entryPoint the main method to analyze
	 * @param sourcesSinks manager class for identifying sources and sinks in the source code
	 */
	public void computeInfoflow(String path, String entryPoint, ISourceSinkManager sourcesSinks);

	/**
	 * getResults returns the results found by the analysis
	 * @return the results
	 */
	public InfoflowResults getResults();
	
	/**
	 * A result is available if the analysis has finished - so if this method returns false the
	 * analysis has not finished yet or was not started (e.g. no sources or sinks found)
	 * @return boolean that states if a result is available
	 */
	public boolean isResultAvailable();
	
	/**
	 * default: inspectSources is set to true, this means sources are analyzed as well.
	 * If inspectSources is set to false, then the analysis does not propagate values into 
	 * the source method.
	 * @param inspect boolean that determines the inspectSource option
	 */
	public void setInspectSources(boolean inspect);

	/**
	 * default: inspectSinks is set to true, this means sinks are analyzed as well.
	 * If inspectSinks is set to false, then the analysis does not propagate values into 
	 * the sink method.
	 * @param inspect boolean that determines the inspectSink option
	 */
	public void setInspectSinks(boolean inspect);
	
	/**
	 * Sets whether the solver shall consider implicit flows.
	 * @param enableImplicitFlows True if implicit flows shall be considered,
	 * otherwise false.
	 */
	public void setEnableImplicitFlows(boolean enableImplicitFlows);

	/**
	 * Sets whether the solver shall consider assignments to static fields
	 * @param enableStaticFields True if assignments to static fields shall be
	 * considered, otherwise false
	 */
	public void setEnableStaticFieldTracking(boolean enableStaticFields);
	
	/**
	 * Sets whether the solver shall compute the paths between the sources and
	 * sinks instead of just reporting if there is a path or not.
	 * @param computeResultPaths True if paths shall be computed, otherwise false
	 */
	public void setComputeResultPaths(boolean computeResultPaths);

	/**
	 * Sets whether a flow sensitive aliasing algorithm shall be used
	 * @param flowSensitiveAliasing True if a flow sensitive aliasing algorithm
	 * shall be used, otherwise false
	 */
	public void setFlowSensitiveAliasing(boolean flowSensitiveAliasing);

	/**
	 * Sets whether the solver shall track taints of thrown exception objects
	 * @param enableExceptions True if taints associated with exceptions shall
	 * be tracked over try/catch construct, otherwise false
	 */
	public void setEnableExceptionTracking(boolean enableExceptions);

	/**
	 * Sets the callgraph algorithm to be used by the data flow tracker
	 * @param algorithm The callgraph algorithm to be used by the data flow tracker
	 */
	public void setCallgraphAlgorithm(CallgraphAlgorithm algorithm);
	
	/**
	 * Sets the aliasing algorithm to be used by the data flow tracker
	 * @param algorithm The aliasing algorithm to be used by the data flow tracker
	 */
	public void setAliasingAlgorithm(AliasingAlgorithm algorithm);
	
	/**
	 * Sets the maximum number of threads to be used by the solver. A value of -1
	 * indicates an unlimited number of threads, i.e., there will be as many threads
	 * as there are CPU cores on the machine.
	 * @param threadNum The maximum number of threads to be used by the solver,
	 * or -1 for an unlimited number of threads.
	 */
	public void setMaxThreadNum(int threadNum);
	
}
