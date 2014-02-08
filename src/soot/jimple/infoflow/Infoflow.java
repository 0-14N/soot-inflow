/*******************************************************************************
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.Main;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.entryPointCreators.IEntryPointCreator;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.handlers.TaintPropagationHandler;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.infoflow.util.SootMethodRepresentationParser;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.options.Options;
import soot.shoon.android.analysis.AnalysisManager;
import soot.shoon.android.analysis.SingleMethodAnalysis;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.ClassicCompleteBlockGraph;
/**
 * main infoflow class which triggers the analysis and offers method to customize it.
 *
 */
public class Infoflow extends AbstractInfoflow {
	
    private final Logger logger = LoggerFactory.getLogger(getClass());

	private static boolean debug = false;
	private static int accessPathLength = 5;
	
	private InfoflowResults results;

	private final String androidPath;
	private final boolean forceAndroidJar;
	private IInfoflowConfig sootConfig;
	
    private IInfoflowCFG iCfg;
    
    private Set<ResultsAvailableHandler> onResultsAvailable = new HashSet<ResultsAvailableHandler>();
    private Set<TaintPropagationHandler> taintPropagationHandlers = new HashSet<TaintPropagationHandler>();
    private String sootArgs[] = new String[0];

	/**
	 * Creates a new instance of the InfoFlow class for analyzing plain Java code without any references to APKs or the Android SDK.
	 */
	public Infoflow() {
		this.androidPath = "";
		this.forceAndroidJar = false;
	}

	/**
	 * Creates a new instance of the Infoflow class for analyzing Android APK files.
	 * @param androidPath If forceAndroidJar is false, this is the base directory
	 * of the platform files in the Android SDK. If forceAndroidJar is true, this
	 * is the full path of a single android.jar file.
	 * @param forceAndroidJar True if a single platform JAR file shall be forced,
	 * false if Soot shall pick the appropriate platform version 
	 */
	public Infoflow(String androidPath, boolean forceAndroidJar) {
		super();
		this.androidPath = androidPath;
		this.forceAndroidJar = forceAndroidJar;
	}

	/**
	 * Creates a new instance of the Infoflow class for analyzing Android APK files.
	 * @param androidPath If forceAndroidJar is false, this is the base directory
	 * of the platform files in the Android SDK. If forceAndroidJar is true, this
	 * is the full path of a single android.jar file.
	 * @param forceAndroidJar True if a single platform JAR file shall be forced,
	 * false if Soot shall pick the appropriate platform version
	 * @param icfgFactory The interprocedural CFG to be used by the InfoFlowProblem 
	 */
	public Infoflow(String androidPath, boolean forceAndroidJar, BiDirICFGFactory icfgFactory) {
		super(icfgFactory);
		this.androidPath = androidPath;
		this.forceAndroidJar = forceAndroidJar;
	}

	public static void setDebug(boolean debugflag) {
		debug = debugflag;
	}
	
	public void setSootConfig(IInfoflowConfig config){
		sootConfig = config;
	}
	
	/**
	 * Initializes Soot.
	 * @param path The Soot classpath
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds.
	 * @param sourcesSinks The manager object for identifying sources and sinks
	 */
	private void initializeSoot(String path, Set<String> classes, ISourceSinkManager sourcesSinks) {
		initializeSoot(path, classes, sourcesSinks, "");
	}
	
	/**
	 * Initializes Soot.
	 * @param path The Soot classpath
	 * @param classes The set of classes that shall be checked for data flow
	 * analysis seeds. All sources in these classes are used as seeds. If a
	 * non-empty extra seed is given, this one is used too.
	 * @param sourcesSinks The manager object for identifying sources and sinks
	 * @param extraSeed An optional extra seed, can be empty.
	 */
	private void initializeSoot(String path, Set<String> classes, ISourceSinkManager sourcesSinks, String extraSeed) {
		// reset Soot:
		logger.info("Resetting Soot...");
		soot.G.reset();
		
		// add SceneTransformer which calculates and prints infoflow
		Set<String> seeds = Collections.emptySet();
		if (extraSeed != null && !extraSeed.isEmpty())
			seeds = Collections.singleton(extraSeed);
		addSceneTransformer(sourcesSinks, seeds);

		Options.v().set_no_bodies_for_excluded(true);//==> "-no-bodies-for-excluded"
		Options.v().set_allow_phantom_refs(true);//==> "-allow-phantom-refs"
		if (debug){
			Options.v().set_output_format(Options.output_format_shimple);
		}else{
			Options.v().set_output_format(Options.output_format_shimple);//==> "-f S"
		}
		Options.v().set_via_shimple(true);//==> "-via-shimple"
		Options.v().set_whole_shimple(true);//==> "-ws"
		Options.v().setPhaseOption("wstp", "enabled:true");//==>
		Options.v().set_soot_classpath(path);//==> "-cp path"
		Options.v().set_process_dir(new ArrayList<String>(classes));//==> "-process-path classes"

		// Configure the callgraph algorithm
		switch (callgraphAlgorithm) {
			case AutomaticSelection:
				if (extraSeed == null || extraSeed.isEmpty()){
					Options.v().setPhaseOption("cg.spark", "on");//==> "-p cg.spark"
				}
				else{
					Options.v().setPhaseOption("cg.spark", "vta:true");//==> "vta:true"
				}
				break;
			case RTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "rta:true");
				break;
			case VTA:
				Options.v().setPhaseOption("cg.spark", "on");
				Options.v().setPhaseOption("cg.spark", "vta:true");
				break;
			default:
				throw new RuntimeException("Invalid callgraph algorithm");
		}
		// do not merge variables (causes problems with PointsToSets)
		//jb.ulp -- Local packer: minimizes number of locals
		//Options.v().setPhaseOption("jb.ulp", "off");
		
		//Removes redundant static initializer calls
		Options.v().setPhaseOption("cg", "trim-clinit:false");//==>"cg trim-clinit:false"
		
		if (!this.androidPath.isEmpty()) {
			Options.v().set_src_prec(Options.src_prec_apk);//==> "-src-prec apk"
			if (this.forceAndroidJar){
				soot.options.Options.v().set_force_android_jar(this.androidPath);//==>"-force-android-jar PATH"
			}
			else{
				soot.options.Options.v().set_android_jars(this.androidPath);//==> "-android-jars PATH"
			}
		} else{
			Options.v().set_src_prec(Options.src_prec_java);
		}
		
		//at the end of setting: load user settings:
		if (sootConfig != null)
			sootConfig.setSootOptions(Options.v());
		
		// load all entryPoint classes with their bodies
		Scene.v().loadNecessaryClasses();
		//Main.v().main(sootArgs);
		boolean hasClasses = false;
		for (String className : classes) {
			SootClass c = Scene.v().forceResolve(className, SootClass.BODIES);
			if (c != null){
				c.setApplicationClass();
				if(!c.isPhantomClass() && !c.isPhantom())
					hasClasses = true;
			}
		}
		if (!hasClasses) {
			logger.error("Only phantom classes loaded, skipping analysis...");
			return;
		}

	}

	@Override
	public void computeInfoflow(String path, IEntryPointCreator entryPointCreator,
			List<String> entryPoints, ISourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			logger.error("Sources are empty!");
			return;
		}
	
		initializeSoot(path,
				SootMethodRepresentationParser.v().parseClassNames(entryPoints, false).keySet(),
				sourcesSinks);

		// entryPoints are the entryPoints required by Soot to calculate Graph - if there is no main method,
		// we have to create a new main method and use it as entryPoint and store our real entryPoints
		Scene.v().setEntryPoints(Collections.singletonList(entryPointCreator.createDummyMain(entryPoints)));

		// We explicitly select the packs we want to run for performance reasons
        PackManager.v().getPack("wspp").apply();//==>
        PackManager.v().getPack("cg").apply();//==>
        PackManager.v().getPack("wjtp").apply();
        PackManager.v().getPack("wstp").apply();//==>
        //Main.v().main(args); ==>
		if (debug)
			PackManager.v().writeOutput();
	}


	@Override
	public void computeInfoflow(String path, String entryPoint, ISourceSinkManager sourcesSinks) {
		results = null;
		if (sourcesSinks == null) {
			logger.error("Sources are empty!");
			return;
		}

		initializeSoot(path, SootMethodRepresentationParser.v().parseClassNames
				(Collections.singletonList(entryPoint), false).keySet(), sourcesSinks, entryPoint);

		if (!Scene.v().containsMethod(entryPoint)){
			logger.error("Entry point not found: " + entryPoint);
			return;
		}
		SootMethod ep = Scene.v().getMethod(entryPoint);
		if (ep.isConcrete())
			ep.retrieveActiveBody();
		else {
			logger.debug("Skipping non-concrete method " + ep);
			return;
		}
		Scene.v().setEntryPoints(Collections.singletonList(ep));
		Options.v().set_main_class(ep.getDeclaringClass().getName());
		
		// We explicitly select the packs we want to run for performance reasons
        PackManager.v().getPack("wspp").apply();
        PackManager.v().getPack("cg").apply();
        PackManager.v().getPack("wjtp").apply();
        PackManager.v().getPack("wstp").apply();
		if (debug)
			PackManager.v().writeOutput();
	}

	private void addSceneTransformer(final ISourceSinkManager sourcesSinks, final Set<String> additionalSeeds) {
		Transform transform = new Transform("wstp.analysis", new SceneTransformer() {
			protected void internalTransform(String phaseName, @SuppressWarnings("rawtypes") Map options) {
                logger.info("Shimple Callgraph has {} edges", Scene.v().getCallGraph().size());
                iCfg = icfgFactory.buildBiDirICFG();
                
                if(iCfg == null){
                	logger.info("iCfg is null, exit!");
                	return;
                }
                
                //set the iCfg to AliasBackwardAnalysis
                AnalysisManager.v().setICFG(iCfg);
                AnalysisManager.v().setISSM(sourcesSinks);
                AnalysisManager.v().setITPW(taintWrapper);
                
                int sourceCount = 0;
                int sinkCount = 0;
                				
				//get the sources and sinks
                List<MethodOrMethodContext> eps = new ArrayList<MethodOrMethodContext>(Scene.v().getEntryPoints());
                ReachableMethods reachableMethods = new ReachableMethods(Scene.v().getCallGraph(), eps.iterator(), null);
                reachableMethods.update();
                Map<String, String> classes = new HashMap<String, String>(1000);
                for(Iterator<MethodOrMethodContext> iter = reachableMethods.listener(); iter.hasNext();){
                	SootMethod m = iter.next().method();
                	
                	//save the method 
                	AnalysisManager.v().addMethod(m);
                	
                	if(m.hasActiveBody()){
                		//Collect the Jimple bodies
                		//if(debug){
                		if(true){
                			String className = m.getDeclaringClass().getName();
                			if(classes.containsKey(className)){
                				classes.put(className, classes.get(className) + m.getActiveBody().toString());
                			}else{
                				classes.put(className, m.getActiveBody().toString());
                			}
                		}
                		
                		//For each reachable methods, find the sources and sinks.
                		//Divide the method to basic blocks, iterate the blocks to find the sources
                		//and sinks
                		ClassicCompleteBlockGraph ccbg = new ClassicCompleteBlockGraph(m.getActiveBody());
                		List<Block> blocks = ccbg.getBlocks();
                		for(Block b : blocks){
                			for(Iterator<Unit> it = b.iterator(); it.hasNext();){
                				Unit u = it.next();
                				//if(sourcesSinks.isSource((Stmt) u, iCfg)){
                				if(sourcesSinks.isMySource((Stmt) u)){
                    				logger.info("Source found: {}-->{}", iCfg.getMethodOf(u), u);
                    				SingleMethodAnalysis sma = new SingleMethodAnalysis(m, ccbg, b, u);
                    				//record the source
                    				AnalysisManager.v().addSource(sma);
                    				sourceCount++;
                    			}
                    			//if(sourcesSinks.isSink((Stmt) u, iCfg)){
                				if(sourcesSinks.isMySink((Stmt) u)){
                    				logger.info("Sink found: {}-->{}", iCfg.getMethodOf(u), u);
                    				//record the sink
                    				AnalysisManager.v().addSink(b, u);
                    				sinkCount++;
                    			}
                			}
                		}
                	}
                }
                
                //Save Jimple files to "JimpleFiles/"
                //if(debug){
                if(true){
                	File dir = new File("ShimpleFiles");
                	if(!dir.exists()){
                		dir.mkdir();
                	}else{
                		for(File f : dir.listFiles()){
                			f.delete();
                		}
                	}
                	for(Entry<String, String> entry : classes.entrySet()){
                		try{
                			stringToTextFile(new File(".").getAbsoluteFile() + System.getProperty("file.separator") + "ShimpleFiles"
                					+ System.getProperty("file.separator") + entry.getKey() + ".shimple", entry.getValue());
                		}catch(IOException e){
                			logger.error("Could not write jimple file: {}", entry.getKey() + ".shimple", e);
                		}
                	}
                }
                
                if(sourceCount == 0 || sinkCount == 0){
                	logger.info("{} sources, {} sinks! exit!", sourceCount, sinkCount);
                }else{
                	//start alias analysis
                	AnalysisManager.v().start();
                }
                
			}
			
		});

		
        for (Transform tr : preProcessors){
            PackManager.v().getPack("wstp").add(tr);
        }
		//PackManager.v().getPack("wjtp").add(transform);
		PackManager.v().getPack("wstp").add(transform);
	}

		private void stringToTextFile(String fileName, String contents) throws IOException {
			BufferedWriter wr = null;
			try {
				wr = new BufferedWriter(new FileWriter(fileName));
				wr.write(contents);
				wr.flush();
			}
			finally {
				if (wr != null)
					wr.close();
			}
		}

	@Override
	public InfoflowResults getResults() {
		return results;
	}

	@Override
	public boolean isResultAvailable() {
		if (results == null) {
			return false;
		}
		return true;
	}

	
	public static int getAccessPathLength() {
		return accessPathLength;
	}
	
	/**
	 * Sets the maximum depth of the access paths. All paths will be truncated
	 * if they exceed the given size.
	 * @param accessPathLength the maximum value of an access path. If it gets longer than
	 *  this value, it is truncated and all following fields are assumed as tainted 
	 *  (which is imprecise but gains performance)
	 *  Default value is 5.
	 */
	public void setAccessPathLength(int accessPathLength) {
		Infoflow.accessPathLength = accessPathLength;
	}
	
	/**
	 * Adds a handler that is called when information flow results are available
	 * @param handler The handler to add
	 */
	public void addResultsAvailableHandler(ResultsAvailableHandler handler) {
		this.onResultsAvailable.add(handler);
	}
	
	/**
	 * Adds a handler which is invoked whenever a taint is propagated
	 * @param handler The handler to be invoked when propagating taints
	 */
	public void addTaintPropagationHandler(TaintPropagationHandler handler) {
		this.taintPropagationHandlers.add(handler);
	}
	
	/**
	 * Removes a handler that is called when information flow results are available
	 * @param handler The handler to remove
	 */
	public void removeResultsAvailableHandler(ResultsAvailableHandler handler) {
		onResultsAvailable.remove(handler);
	}
	
}
