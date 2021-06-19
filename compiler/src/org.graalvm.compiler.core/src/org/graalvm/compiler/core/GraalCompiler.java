/*
 * Copyright (c) 2009, 2020, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package org.graalvm.compiler.core;

import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaType;
import org.graalvm.compiler.code.CompilationResult;
import org.graalvm.compiler.core.common.PermanentBailoutException;
import org.graalvm.compiler.core.common.RetryableBailoutException;
import org.graalvm.compiler.core.common.type.StampFactory;
import org.graalvm.compiler.core.common.util.CompilationAlarm;
import org.graalvm.compiler.core.target.Backend;
import org.graalvm.compiler.debug.DebugCloseable;
import org.graalvm.compiler.debug.DebugContext;
import org.graalvm.compiler.debug.DebugContext.CompilerPhaseScope;
import org.graalvm.compiler.debug.MethodFilter;
import org.graalvm.compiler.debug.TimerKey;
import org.graalvm.compiler.graph.Node;
import org.graalvm.compiler.graph.iterators.NodeIterable;
import org.graalvm.compiler.lir.asm.CompilationResultBuilderFactory;
import org.graalvm.compiler.lir.phases.LIRSuites;
import org.graalvm.compiler.nodes.BeginNode;
import org.graalvm.compiler.nodes.ConstantNode;
import org.graalvm.compiler.nodes.EndNode;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.FrameState;
import org.graalvm.compiler.nodes.IfNode;
import org.graalvm.compiler.nodes.InvokeNode;
import org.graalvm.compiler.nodes.LoopBeginNode;
import org.graalvm.compiler.nodes.LoopEndNode;
import org.graalvm.compiler.nodes.LoopExitNode;
import org.graalvm.compiler.nodes.MergeNode;
import org.graalvm.compiler.nodes.StateSplit;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.ValueNode;
import org.graalvm.compiler.nodes.ValuePhiNode;
import org.graalvm.compiler.nodes.ValueProxyNode;
import org.graalvm.compiler.nodes.calc.AddNode;
import org.graalvm.compiler.nodes.calc.IntegerEqualsNode;
import org.graalvm.compiler.nodes.calc.IntegerLessThanNode;
import org.graalvm.compiler.nodes.calc.MulNode;
import org.graalvm.compiler.nodes.calc.SignExtendNode;
import org.graalvm.compiler.nodes.calc.SubNode;
import org.graalvm.compiler.nodes.extended.OSRLocalNode;
import org.graalvm.compiler.nodes.java.ArrayLengthNode;
import org.graalvm.compiler.nodes.java.InstanceOfNode;
import org.graalvm.compiler.nodes.java.LoadFieldNode;
import org.graalvm.compiler.nodes.java.LoadIndexedNode;
import org.graalvm.compiler.nodes.java.NewArrayNode;
import org.graalvm.compiler.nodes.java.StoreIndexedNode;
import org.graalvm.compiler.phases.OptimisticOptimizations;
import org.graalvm.compiler.phases.PhaseSuite;
import org.graalvm.compiler.phases.common.DeadCodeEliminationPhase;
import org.graalvm.compiler.phases.tiers.HighTierContext;
import org.graalvm.compiler.phases.tiers.LowTierContext;
import org.graalvm.compiler.phases.tiers.MidTierContext;
import org.graalvm.compiler.phases.tiers.Suites;
import org.graalvm.compiler.phases.tiers.SuperHighTierContext;
import org.graalvm.compiler.phases.tiers.TargetProvider;
import org.graalvm.compiler.phases.util.GraphOrder;
import org.graalvm.compiler.phases.util.Providers;

import jdk.vm.ci.meta.ProfilingInfo;
import jdk.vm.ci.meta.ResolvedJavaMethod;

import java.util.ArrayList;

/**
 * Static methods for orchestrating the compilation of a {@linkplain StructuredGraph graph}.
 */
public class GraalCompiler {

  private static final TimerKey CompilerTimer = DebugContext.timer("GraalCompiler").doc("Time spent in compilation (excludes code installation).");
  private static final TimerKey FrontEnd = DebugContext.timer("FrontEnd").doc("Time spent processing HIR.");

  // lambdaCall could be an array list of pairs(?) if we need more than
  // one lambdas and in pair it will also store an identity to be called
  private static LambdaFunction lambdaCall;
  private static Node dataNode;
  private static boolean firstTime = true;
  private static ArrayList<Node> bindNodes = new ArrayList<>();


  /**
   * Encapsulates all the inputs to a {@linkplain GraalCompiler#compile(Request) compilation}.
   */
  public static class Request<T extends CompilationResult> {
    public final StructuredGraph graph;
    public final ResolvedJavaMethod installedCodeOwner;
    public final Providers providers;
    public final Backend backend;
    public final PhaseSuite<HighTierContext> graphBuilderSuite;
    public final OptimisticOptimizations optimisticOpts;
    public final ProfilingInfo profilingInfo;
    public final Suites suites;
    public final LIRSuites lirSuites;
    public final T compilationResult;
    public final CompilationResultBuilderFactory factory;
    public final boolean verifySourcePositions;

    /**
     * @param graph              the graph to be compiled
     * @param installedCodeOwner the method the compiled code will be associated with once
     *                           installed. This argument can be null.
     * @param providers
     * @param backend
     * @param graphBuilderSuite
     * @param optimisticOpts
     * @param profilingInfo
     * @param suites
     * @param lirSuites
     * @param compilationResult
     * @param factory
     */
    public Request(StructuredGraph graph, ResolvedJavaMethod installedCodeOwner, Providers providers, Backend backend, PhaseSuite<HighTierContext> graphBuilderSuite,
                   OptimisticOptimizations optimisticOpts, ProfilingInfo profilingInfo, Suites suites, LIRSuites lirSuites, T compilationResult, CompilationResultBuilderFactory factory,
                   boolean verifySourcePositions) {
      this.graph = graph;
      this.installedCodeOwner = installedCodeOwner;
      this.providers = providers;
      this.backend = backend;
      this.graphBuilderSuite = graphBuilderSuite;
      this.optimisticOpts = optimisticOpts;
      this.profilingInfo = profilingInfo;
      this.suites = suites;
      this.lirSuites = lirSuites;
      this.compilationResult = compilationResult;
      this.factory = factory;
      this.verifySourcePositions = verifySourcePositions;
    }

    /**
     * Executes this compilation request.
     *
     * @return the result of the compilation
     */
    public T execute() {
      return GraalCompiler.compile(this);
    }
  }

  /**
   * Requests compilation of a given graph.
   *
   * @param graph              the graph to be compiled
   * @param installedCodeOwner the method the compiled code will be associated with once
   *                           installed. This argument can be null.
   * @return the result of the compilation
   */
  public static <T extends CompilationResult> T compileGraph(StructuredGraph graph, ResolvedJavaMethod installedCodeOwner, Providers providers, Backend backend,
                                                             PhaseSuite<HighTierContext> graphBuilderSuite, OptimisticOptimizations optimisticOpts, ProfilingInfo profilingInfo, Suites suites, LIRSuites lirSuites, T compilationResult,
                                                             CompilationResultBuilderFactory factory, boolean verifySourcePositions) {
    return compile(new Request<>(graph, installedCodeOwner, providers, backend, graphBuilderSuite, optimisticOpts, profilingInfo, suites, lirSuites, compilationResult, factory,
        verifySourcePositions));
  }

  /**
   * Services a given compilation request.
   *
   * @return the result of the compilation
   */
  @SuppressWarnings("try")
  public static <T extends CompilationResult> T compile(Request<T> r) {
    DebugContext debug = r.graph.getDebug();
    try (CompilationAlarm alarm = CompilationAlarm.trackCompilationPeriod(r.graph.getOptions())) {
      assert !r.graph.isFrozen();
      try (DebugContext.Scope s0 = debug.scope("GraalCompiler", r.graph, r.providers.getCodeCache()); DebugCloseable a = CompilerTimer.start(debug)) {
        emitFrontEnd(r.providers, r.backend, r.graph, r.graphBuilderSuite, r.optimisticOpts, r.profilingInfo, r.suites);
        r.backend.emitBackEnd(r.graph, null, r.installedCodeOwner, r.compilationResult, r.factory, null, r.lirSuites);
        if (r.verifySourcePositions) {
          assert r.graph.verifySourcePositions(true);
        }
      } catch (Throwable e) {
        throw debug.handle(e);
      }
      checkForRequestedCrash(r.graph);
      return r.compilationResult;
    }
  }

  /**
   * Checks whether the {@link GraalCompilerOptions#CrashAt} option indicates that the compilation
   * of {@code graph} should result in an exception.
   *
   * @param graph a graph currently being compiled
   * @throws RuntimeException if the value of {@link GraalCompilerOptions#CrashAt} matches
   *                          {@code graph.method()} or {@code graph.name}
   */
  private static void checkForRequestedCrash(StructuredGraph graph) {
    String value = GraalCompilerOptions.CrashAt.getValue(graph.getOptions());
    if (value != null) {
      boolean bailout = false;
      boolean permanentBailout = false;
      String methodPattern = value;
      if (value.endsWith(":Bailout")) {
        methodPattern = value.substring(0, value.length() - ":Bailout".length());
        bailout = true;
      } else if (value.endsWith(":PermanentBailout")) {
        methodPattern = value.substring(0, value.length() - ":PermanentBailout".length());
        permanentBailout = true;
      }
      String crashLabel = null;
      if (graph.name != null && graph.name.contains(methodPattern)) {
        crashLabel = graph.name;
      }
      if (crashLabel == null) {
        ResolvedJavaMethod method = graph.method();
        MethodFilter filter = MethodFilter.parse(methodPattern);
        if (filter.matches(method)) {
          crashLabel = method.format("%H.%n(%p)");
        }
      }
      if (crashLabel != null) {
        String crashMessage = "Forced crash after compiling " + crashLabel;
        notifyCrash(crashMessage);
        if (permanentBailout) {
          throw new PermanentBailoutException(crashMessage);
        }
        if (bailout) {
          throw new RetryableBailoutException(crashMessage);
        }
        throw new RuntimeException(crashMessage);
      }
    }
  }

  /**
   * Substituted by {@code com.oracle.svm.graal.hotspot.libgraal.
   * Target_org_graalvm_compiler_core_GraalCompiler} to optionally test routing fatal error
   * handling from libgraal to HotSpot.
   */
  @SuppressWarnings("unused")
  private static void notifyCrash(String crashMessage) {
  }

  /**
   * Builds the graph, optimizes it.
   */
  @SuppressWarnings("try")
  public static void emitFrontEnd(Providers providers, TargetProvider target, StructuredGraph graph, PhaseSuite<HighTierContext> graphBuilderSuite, OptimisticOptimizations optimisticOpts,
                                  ProfilingInfo profilingInfo, Suites suites) {
    DebugContext debug = graph.getDebug();
    try (DebugContext.Scope s = debug.scope("FrontEnd"); DebugCloseable a = FrontEnd.start(debug)) {
      HighTierContext highTierContext = new HighTierContext(providers, graphBuilderSuite, optimisticOpts);
      SuperHighTierContext superHighTierContext = new SuperHighTierContext(providers, graphBuilderSuite, optimisticOpts);
      if (graph.start().next() == null) {
        try (CompilerPhaseScope cps = debug.enterCompilerPhase("Parsing")) {
          graphBuilderSuite.apply(graph, highTierContext);
          new DeadCodeEliminationPhase(DeadCodeEliminationPhase.Optionality.Optional).apply(graph);
          debug.dump(DebugContext.BASIC_LEVEL, graph, "After parsing");
        }
      } else {
        debug.dump(DebugContext.INFO_LEVEL, graph, "initial state");
      }

      // Iterate through the nodes
      NodeIterable<Node> graphNodes = graph.getNodes();
      for (Node node : graphNodes) {
        matchSecond(node,
            new PatternNode(new StoreIndexedNode()),
            new PatternNode(new StoreIndexedNode()),
            new PatternNode(new InvokeNode(), (x) -> {

              // 2 times are needed the load indexes for values initialization
              // one for current and one for next values
              // TODO: check if this can be reduced to 1, what will happen?
              int totalTimesToFetchLoadIndexed = 2;

              // Duplicate the frame
              // Need to find the best generic class for the stateAfter
              Node nodeIncludingFrameState = x;
              while (!(nodeIncludingFrameState instanceof StateSplit)) {
                nodeIncludingFrameState = nodeIncludingFrameState.predecessor();
              }

              FrameState st = ((StateSplit) nodeIncludingFrameState).stateAfter().duplicate();
              //Keep the connection between start and end node

              //Find the amount of compressed arrays
              int numberOfArrays = 0;
              Node arraySpotted = x.predecessor();
              while (arraySpotted instanceof StoreIndexedNode) {
                numberOfArrays++;
                arraySpotted = arraySpotted.predecessor();
              }

              //Store the ValueNodes with the compressed arrays
              ValueNode[] uncompressedArrayNodes = new ValueNode[numberOfArrays];
              arraySpotted = x.predecessor();
              for (int arrayId = numberOfArrays - 1; arrayId > -1; arrayId--) {
                uncompressedArrayNodes[arrayId] = ((StoreIndexedNode) arraySpotted).value();
                arraySpotted = arraySpotted.predecessor();
              }

              ArrayLengthNode alOfShip = (ArrayLengthNode) bindNodes.get(1);

              ConstantNode constant0 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(0), StampFactory.forInteger(32)));
              ConstantNode constant1 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(1), StampFactory.forInteger(32)));
              ConstantNode constantMinus1 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(-1), StampFactory.forInteger(32)));

              ResolvedJavaType elementType = providers.getMetaAccess().lookupJavaType(Integer.TYPE);

              Node[][] compressedArrayNodes = new Node[numberOfArrays][];
              FixedWithNextNode[] nodesToConnectCompressionLoopWithGraph = new FixedWithNextNode[numberOfArrays + 1];
              nodesToConnectCompressionLoopWithGraph[0] = (FixedWithNextNode) x;

              // Fetch the connection for the end of the compression block
              FixedNode connectAfterCompressionBlock = ((FixedWithNextNode) x).next();


              for (int compressEachArray = 0; compressEachArray < numberOfArrays; compressEachArray++) {
                compressedArrayNodes[compressEachArray] = createCompressedArrayTransformation(graph, elementType,
                    st, nodesToConnectCompressionLoopWithGraph[compressEachArray], uncompressedArrayNodes[compressEachArray], constantMinus1, constant0, constant1);
                //store the array you got to connect the next loop
                nodesToConnectCompressionLoopWithGraph[compressEachArray + 1] = (FixedWithNextNode) compressedArrayNodes[compressEachArray][3];
              }

              ((StoreIndexedNode) compressedArrayNodes[1][3]).setNext(connectAfterCompressionBlock);
              //Node numbers returned from the function inside the for loop above
              /*16*//*18*//*34*//*61*/
              /*64*//*66*//*82*//*108*/


              // Fetch nodes to connect before the operation loop and after the time measurement loop

              /*136*/
              LoopBeginNode operationLoopBegNode = (LoopBeginNode) bindNodes.get(0);
              FrameState stateOfOperationLoop = operationLoopBegNode.stateAfter().duplicate();

              EndNode endBeforeLoop = null;
              for (Node en : operationLoopBegNode.forwardEnds().snapshot()) {
                endBeforeLoop = (EndNode) en;
              }


              FixedWithNextNode addLoadIndexedBeforeThisNode = (FixedWithNextNode) endBeforeLoop.predecessor();


              LoadIndexedNode[][] loadValuesArraysForNextAndCurrent = new LoadIndexedNode[2][2];
              FixedWithNextNode previousNodeOfGraphConnectedWithLoadIndBlock = addLoadIndexedBeforeThisNode;

              for (int fetchedAllArraysLoad = 0; fetchedAllArraysLoad < totalTimesToFetchLoadIndexed; fetchedAllArraysLoad++) {
                for (int arrayFetched = 0; arrayFetched < numberOfArrays; arrayFetched++) {
                  loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched] = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[arrayFetched][0], constant0, null, JavaKind.Int));
                  previousNodeOfGraphConnectedWithLoadIndBlock.setNext(loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched]);
                  previousNodeOfGraphConnectedWithLoadIndBlock = loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched];
                }
              }


              loadValuesArraysForNextAndCurrent[totalTimesToFetchLoadIndexed - 1][numberOfArrays - 1].setNext(endBeforeLoop);

              //Arrays initialized and used later for the automated creation
              ValuePhiNode[] finishArrayBooleans = new ValuePhiNode[numberOfArrays];
              AddNode[] increaseIterPointer = new AddNode[numberOfArrays];


              // An array of phi nodes to keep the iterationPointers that show to the start positions
              ValuePhiNode[] iterationPointers = new ValuePhiNode[numberOfArrays];
              for (int iter = 0; iter < numberOfArrays; iter++) {
                iterationPointers[iter] = graph.addWithoutUnique(
                    new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
                );
                iterationPointers[iter].addInput(constant0);
              } /*138 139*/

              // An array of phi nodes to keep the compressed values needed for this iteration
              ValuePhiNode[] currentArrayValues = new ValuePhiNode[numberOfArrays];
              for (int currentVal = 0; currentVal < numberOfArrays; currentVal++) {
                currentArrayValues[currentVal] = graph.addWithoutUnique(
                    new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
                );
                currentArrayValues[currentVal].addInput(loadValuesArraysForNextAndCurrent[0][currentVal]);
              }/*140 141*/

              // An array of phi nodes to keep the compressed values fetched using the pointers for the next iteration
              ValuePhiNode[] nextArrayValues = new ValuePhiNode[numberOfArrays];
              for (int nextVal = 0; nextVal < numberOfArrays; nextVal++) {
                nextArrayValues[nextVal] = graph.addWithoutUnique(
                    new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
                );
                nextArrayValues[nextVal].addInput(loadValuesArraysForNextAndCurrent[1][nextVal]);
              }/*142 143*/

              /*144*/
              ValuePhiNode currentIteratorVal = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              currentIteratorVal.addInput(constant0);

              /*145*/
              ValuePhiNode nextMinIteratorVal = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              nextMinIteratorVal.addInput(constantMinus1);

              /* old 53*/
              LoadIndexedNode loadForFirstPredicateToBeDeleted = (LoadIndexedNode) bindNodes.get(2);

              /*163*/
              BeginNode startTheOperationLoop = (BeginNode) loadForFirstPredicateToBeDeleted.predecessor();

              /*165*/
              IntegerEqualsNode conditionToCalculateMinIteratorFirArray = graph.addOrUnique(new IntegerEqualsNode((ValueProxyNode) compressedArrayNodes[0][2], iterationPointers[0]));

              BeginNode begFalseSuccCalculatingMinIterFirArray = graph.add(new BeginNode());
              BeginNode begTrueSuccCalculatingMinIterFirArray = graph.add(new BeginNode());

              IfNode minIteratorFirArrayCondition = graph.add(new IfNode(conditionToCalculateMinIteratorFirArray, begTrueSuccCalculatingMinIterFirArray, begFalseSuccCalculatingMinIterFirArray, 0.1));
              startTheOperationLoop.setNext(minIteratorFirArrayCondition);

              AddNode increaseFirArrIterPointer = graph.addWithoutUnique(new AddNode(iterationPointers[0], constant1));

              // Store it for use in next compressed values automation
              increaseIterPointer[0] = increaseFirArrIterPointer;

              /*170*/
              LoadIndexedNode loadFirArrayNextStartPos = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][1], increaseFirArrIterPointer, null, JavaKind.Int));
              begFalseSuccCalculatingMinIterFirArray.setNext(loadFirArrayNextStartPos);

              /*171*/
              EndNode endTrueSuccessorCalculatingMinIterFirArr = graph.addWithoutUnique(new EndNode());
              begTrueSuccCalculatingMinIterFirArray.setNext(endTrueSuccessorCalculatingMinIterFirArr);

              /*173*/
              EndNode endFalseSuccessorCalculatingMinIterFirArr = graph.addWithoutUnique(new EndNode());
              loadFirArrayNextStartPos.setNext(endFalseSuccessorCalculatingMinIterFirArr);

              /*172*/
              MergeNode mergeCalculatingMinIterFirArraySuccessors = graph.add(new MergeNode());
              mergeCalculatingMinIterFirArraySuccessors.addForwardEnd(endTrueSuccessorCalculatingMinIterFirArr);
              mergeCalculatingMinIterFirArraySuccessors.addForwardEnd(endFalseSuccessorCalculatingMinIterFirArr);
              mergeCalculatingMinIterFirArraySuccessors.setStateAfter(stateOfOperationLoop);

              /*174*/
              ValuePhiNode nextMinIteratorValForFirArrayMergeCalc = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeCalculatingMinIterFirArraySuccessors)
              );
              nextMinIteratorValForFirArrayMergeCalc.addInput(nextMinIteratorVal);
              nextMinIteratorValForFirArrayMergeCalc.addInput(loadFirArrayNextStartPos);

              /*175*/
              ValuePhiNode finishFirArrayBoolean = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeCalculatingMinIterFirArraySuccessors)
              );
              finishFirArrayBoolean.addInput(constant1);
              finishFirArrayBoolean.addInput(constant0);

              // Store it for use in next compressed values automation
              finishArrayBooleans[0] = finishFirArrayBoolean;

              /*177*/
              IntegerEqualsNode conditionToCalculateMinIteratorSeconArray = graph.addOrUnique(new IntegerEqualsNode((ValueProxyNode) compressedArrayNodes[1][2], iterationPointers[1]));

              BeginNode begFalseSuccCalculatingMinIterSeconArray = graph.add(new BeginNode());
              BeginNode begTrueSuccCalculatingMinIterSeconArray = graph.add(new BeginNode());

              IfNode minIteratorSeconArrayCondition = graph.add(new IfNode(conditionToCalculateMinIteratorSeconArray, begTrueSuccCalculatingMinIterSeconArray, begFalseSuccCalculatingMinIterSeconArray, 0.1));
              mergeCalculatingMinIterFirArraySuccessors.setNext(minIteratorSeconArrayCondition);

              AddNode increaseSeconIterPointer = graph.addWithoutUnique(new AddNode(iterationPointers[1], constant1));

              // Store it for use in next compressed values automation
              increaseIterPointer[1] = increaseSeconIterPointer;

              /*182*/
              LoadIndexedNode loadSeconArrayNextStartPos = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][1], increaseSeconIterPointer, null, JavaKind.Int));
              begFalseSuccCalculatingMinIterSeconArray.setNext(loadSeconArrayNextStartPos);

              IntegerLessThanNode conditionSeconArrayStartPosAndMinIter = graph.addWithoutUnique(new IntegerLessThanNode(loadSeconArrayNextStartPos, nextMinIteratorValForFirArrayMergeCalc));

              /*188*/
              BeginNode begTrueSuccForSeconArrayStartAndMinIter = graph.add(new BeginNode());
              BeginNode begFalseSuccForSeconArrayStartAndMinIter = graph.add(new BeginNode());

              IfNode seconArrayStartAndMinIterCondition = graph.add(new IfNode(conditionSeconArrayStartPosAndMinIter, begTrueSuccForSeconArrayStartAndMinIter, begFalseSuccForSeconArrayStartAndMinIter, 0.1));
              loadSeconArrayNextStartPos.setNext(seconArrayStartAndMinIterCondition);

              /*191*/
              LoadIndexedNode seconArrayNextStartPosForAssignment = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][1], increaseSeconIterPointer, null, JavaKind.Int));
              begTrueSuccForSeconArrayStartAndMinIter.setNext(seconArrayNextStartPosForAssignment);

              /*184*/
              EndNode endTrueSuccCalculatingMinIterSeconArray = graph.addWithoutUnique(new EndNode());
              begTrueSuccCalculatingMinIterSeconArray.setNext(endTrueSuccCalculatingMinIterSeconArray);

              /*186*/
              EndNode endFalseSuccForSeconArrayStartAndMinIter = graph.addWithoutUnique(new EndNode());
              begFalseSuccForSeconArrayStartAndMinIter.setNext(endFalseSuccForSeconArrayStartAndMinIter);

              /*192*/
              EndNode endTrueSuccForSeconArrayStartAndMinIter = graph.addWithoutUnique(new EndNode());
              seconArrayNextStartPosForAssignment.setNext(endTrueSuccForSeconArrayStartAndMinIter);

              /*185*/
              MergeNode seconArrayStartPosAndMinIterMerge = graph.add(new MergeNode());
              seconArrayStartPosAndMinIterMerge.addForwardEnd(endTrueSuccCalculatingMinIterSeconArray);
              seconArrayStartPosAndMinIterMerge.addForwardEnd(endFalseSuccForSeconArrayStartAndMinIter);
              seconArrayStartPosAndMinIterMerge.addForwardEnd(endTrueSuccForSeconArrayStartAndMinIter);
              seconArrayStartPosAndMinIterMerge.setStateAfter(stateOfOperationLoop);

              /*187*/
              ValuePhiNode finishedSeconArrayBooleanAfterMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), seconArrayStartPosAndMinIterMerge)
              );
              finishedSeconArrayBooleanAfterMerge.addInput(constant1);
              finishedSeconArrayBooleanAfterMerge.addInput(constant0);
              finishedSeconArrayBooleanAfterMerge.addInput(constant0);

              // Store it for use in next compressed values automation
              finishArrayBooleans[1] = finishedSeconArrayBooleanAfterMerge;

              /*193*/
              ValuePhiNode minNextIterAfterSeconArrAndMinIterMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), seconArrayStartPosAndMinIterMerge)
              );
              minNextIterAfterSeconArrAndMinIterMerge.addInput(nextMinIteratorValForFirArrayMergeCalc);
              minNextIterAfterSeconArrAndMinIterMerge.addInput(nextMinIteratorValForFirArrayMergeCalc);
              minNextIterAfterSeconArrAndMinIterMerge.addInput(seconArrayNextStartPosForAssignment);

              currentIteratorVal.addInput(minNextIterAfterSeconArrAndMinIterMerge);
              nextMinIteratorVal.addInput(minNextIterAfterSeconArrAndMinIterMerge);

              FixedWithNextNode connectNextCompressionValueWithGraph = seconArrayStartPosAndMinIterMerge;


              for (int createNextCompressionValue = 0; createNextCompressionValue < numberOfArrays; createNextCompressionValue++) {
                connectNextCompressionValueWithGraph = fetchTheNextCompressedValue(graph, stateOfOperationLoop, constant0,
                    connectNextCompressionValueWithGraph,
                    finishArrayBooleans[createNextCompressionValue], compressedArrayNodes[createNextCompressionValue],
                    increaseIterPointer[createNextCompressionValue], minNextIterAfterSeconArrAndMinIterMerge,
                    iterationPointers[createNextCompressionValue], nextArrayValues[createNextCompressionValue], currentArrayValues[createNextCompressionValue]);
              } /*202*//*219*/

              /*229*/
              IntegerEqualsNode conditionMinIterMinusOne = graph.addOrUnique(new IntegerEqualsNode(minNextIterAfterSeconArrAndMinIterMerge, constantMinus1));

              BeginNode begFalseMinIterMinusOne = graph.add(new BeginNode());
              BeginNode begTrueMinIterMinusOne = graph.add(new BeginNode());

              IfNode MinIterMinusOneCheck = graph.add(new IfNode(conditionMinIterMinusOne, begTrueMinIterMinusOne, begFalseMinIterMinusOne, 0.1));
              connectNextCompressionValueWithGraph.setNext(MinIterMinusOneCheck);

              /*233*/
              ArrayLengthNode uncompArrayLengthForLastIteration = graph.add(new ArrayLengthNode(uncompressedArrayNodes[0]));
              begTrueMinIterMinusOne.setNext(uncompArrayLengthForLastIteration);

              SubNode lengthForLastPositionSubtraction = graph.addWithoutUnique(new SubNode(uncompArrayLengthForLastIteration, currentIteratorVal));

              /*236*/
              SubNode lengthFromMinIterSubtraction = graph.addWithoutUnique(new SubNode(minNextIterAfterSeconArrAndMinIterMerge, currentIteratorVal));

              EndNode endTrueMinIterMinusOne = graph.addWithoutUnique(new EndNode());
              uncompArrayLengthForLastIteration.setNext(endTrueMinIterMinusOne);
              /*239*/
              EndNode endFalseMinIterMinusOne = graph.addWithoutUnique(new EndNode());
              begFalseMinIterMinusOne.setNext(endFalseMinIterMinusOne);

              /*238*/
              MergeNode mergeForLength = graph.add(new MergeNode());
              mergeForLength.addForwardEnd(endTrueMinIterMinusOne);
              mergeForLength.addForwardEnd(endFalseMinIterMinusOne);
              mergeForLength.setStateAfter(stateOfOperationLoop);

              /*240*/
              ValuePhiNode lengthBetweenAlignments = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeForLength)
              );
              lengthBetweenAlignments.addInput(lengthForLastPositionSubtraction);
              lengthBetweenAlignments.addInput(lengthFromMinIterSubtraction);


              // get the iterator increase (AddIntegerNode) to change the increasing value

              //Integer less than node which checks the insertion inside the operation loop
              /*149 old 45*/
              IntegerLessThanNode conditionArrayIterationComparison = null;
              for (Node n : alOfShip.usages().snapshot()) {
                if (n instanceof IntegerLessThanNode) {
                  conditionArrayIterationComparison = (IntegerLessThanNode) n;
                }
              }

              //Iterator of the Loop 146 old 42
              ValuePhiNode iteratorInOperationLoop = (ValuePhiNode) conditionArrayIterationComparison.getX();
              /*294 old 94*/
              AddNode iteratorIncrease = null;
              for (Node n : iteratorInOperationLoop.inputs().snapshot()) {
                if (n instanceof AddNode) {
                  iteratorIncrease = (AddNode) n;
                }
              }

              iteratorIncrease.setY(lengthBetweenAlignments);


              // The total number of predicates in the operation loop
              int numberOfPredicates = 3; // TODO: find a way to grab the predicates maybe from the pattern?

              FixedWithNextNode connectWithPreviousGraph = mergeForLength;

              for (int predicateLoad = 0; predicateLoad < numberOfPredicates; predicateLoad++) {
                // Match the LoadIndexed in the predicate with the Array Parameters to locate the correct phi Node
                int arrayAndLoadMatch = -1;
                // Iterate through the number of arrays to compare it with the array in the predicate
                for (int arrayInLoadIndexed = 0; arrayInLoadIndexed < numberOfArrays; arrayInLoadIndexed++) {
                  if (((LoadIndexedNode) bindNodes.get(2 + predicateLoad)).array().equals(uncompressedArrayNodes[arrayInLoadIndexed])) {
                    arrayAndLoadMatch = arrayInLoadIndexed;
                    break;
                  }
                }

                // Use this if in case a predicate does not come from a compressed array
                if (arrayAndLoadMatch > -1) {
                  replaceTheLoadIndexed(graph, (LoadIndexedNode) bindNodes.get(2 + predicateLoad), currentArrayValues[arrayAndLoadMatch], connectWithPreviousGraph);
                  if (predicateLoad < numberOfPredicates - 1) {
                    connectWithPreviousGraph = (FixedWithNextNode) bindNodes.get(2 + predicateLoad + 1).predecessor();
                  }
                }
              }


              //Fetch the sum and SignExtend to use it in the Loop
              /*old 88*/
              LoadIndexedNode loadForSum = (LoadIndexedNode) bindNodes.get(7);

              /*287 old 89*/
              SignExtendNode extendToFitSumLongVal = null;
              for (Node n : loadForSum.usages().snapshot()) {
                if (n instanceof SignExtendNode) {
                  extendToFitSumLongVal = (SignExtendNode) n;
                }
              }

              extendToFitSumLongVal.setValue(currentArrayValues[1]);

              /*288 old 90*/
              AddNode addForSumValue = null;
              for (Node n : extendToFitSumLongVal.usages().snapshot()) {
                if (n instanceof AddNode) {
                  addForSumValue = (AddNode) n;
                }
              }

              /*old 41*/
              ValuePhiNode sumValue = (ValuePhiNode) addForSumValue.getX();

              // Create the new Loop Node to iterate the uncompressed arrays
              LoadIndexedNode loadFirstUncompValue = (LoadIndexedNode) bindNodes.get(5);
              BeginNode begForFirstUncompressedLoad = (BeginNode) loadFirstUncompValue.predecessor();
              /*260*/
              EndNode endBeforeUncompressedInnerOpLoop = graph.addWithoutUnique(new EndNode());
              begForFirstUncompressedLoad.setNext(endBeforeUncompressedInnerOpLoop);

              LoopBeginNode beginUncompressedInnerLoop = graph.add(new LoopBeginNode());
              beginUncompressedInnerLoop.addForwardEnd(endBeforeUncompressedInnerOpLoop);
              beginUncompressedInnerLoop.setStateAfter(stateOfOperationLoop);

              /*262*/
              ValuePhiNode sumForInnerLoop = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(64), beginUncompressedInnerLoop)
              );
              sumForInnerLoop.addInput(sumValue);
              addForSumValue.setX(sumForInnerLoop);

              /*263*/
              ValuePhiNode innerLoopIterator = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), beginUncompressedInnerLoop)
              );
              innerLoopIterator.addInput(constant0);

              /*292*/
              AddNode increaseInnerLoopIterator = graph.addWithoutUnique(new AddNode(innerLoopIterator, constant1));

              innerLoopIterator.addInput(increaseInnerLoopIterator);


              /*265*/
              IntegerLessThanNode conditionForInnerLoop = graph.addWithoutUnique(new IntegerLessThanNode(innerLoopIterator, lengthBetweenAlignments));

              /*267*/
              LoopExitNode exitInnerLoop = graph.add(new LoopExitNode(beginUncompressedInnerLoop));
              exitInnerLoop.setStateAfter(stateOfOperationLoop);

              /*268*/
              ValueProxyNode sendSumFromInnerLoop = graph.addOrUnique(new ValueProxyNode(sumForInnerLoop, exitInnerLoop));


              /*271*/
              BeginNode begInnerLoop = graph.add(new BeginNode());

              IfNode innerLoopEntryCheck = graph.add(new IfNode(conditionForInnerLoop, begInnerLoop, exitInnerLoop, 0.9));
              beginUncompressedInnerLoop.setNext(innerLoopEntryCheck);

              AddNode sumOfInnerAndOuterIterator = graph.addWithoutUnique(new AddNode(iteratorInOperationLoop, innerLoopIterator));

              LoadIndexedNode replaceLoadFirstUncomp = graph.add(new LoadIndexedNode(null, loadFirstUncompValue.array(), sumOfInnerAndOuterIterator, null, JavaKind.Int));
              begInnerLoop.setNext(replaceLoadFirstUncomp);
              /*278 old 81*/
              IfNode nextNodeForFirstLoadCondition = (IfNode) loadFirstUncompValue.next();
              loadFirstUncompValue.setNext(null);
              replaceLoadFirstUncomp.setNext(nextNodeForFirstLoadCondition);
              loadFirstUncompValue.replaceAtUsagesAndDelete(replaceLoadFirstUncomp);

              /*old 80*/
              BeginNode begTrueSuccAfterFirstLoadUncompCheck = (BeginNode) nextNodeForFirstLoadCondition.trueSuccessor();

              /*old End to delete 79*/
              EndNode endOldTrueSuccessorAfterFirstLoad = (EndNode) begTrueSuccAfterFirstLoadUncompCheck.next();

              /*281*/
              EndNode endTrueSuccForSecondInnerLoopCondition = graph.addWithoutUnique(new EndNode());
              begTrueSuccAfterFirstLoadUncompCheck.setNext(endTrueSuccForSecondInnerLoopCondition);

              /*old 82*/
              LoadIndexedNode loadSecondUncompValue = (LoadIndexedNode) bindNodes.get(6);

              /*279*/
              LoadIndexedNode replaceLoadSecondUncomp = graph.add(new LoadIndexedNode(null, loadSecondUncompValue.array(), sumOfInnerAndOuterIterator, null, JavaKind.Int));
              BeginNode begTrueSuccessorSecondLoad = (BeginNode) loadSecondUncompValue.predecessor();
              begTrueSuccessorSecondLoad.setNext(replaceLoadSecondUncomp);
              /*286 old 87*/
              IfNode nextNodeForSecondLoad = (IfNode) loadSecondUncompValue.next();
              loadSecondUncompValue.setNext(null);
              replaceLoadSecondUncomp.setNext(nextNodeForSecondLoad);
              loadSecondUncompValue.replaceAtUsagesAndDelete(replaceLoadSecondUncomp);

              /*284 old 85*/
              BeginNode begTrueSuccessorForLastPredicate = (BeginNode) nextNodeForSecondLoad.trueSuccessor();
              BeginNode begFalseSuccessorForLastPredicate = (BeginNode) nextNodeForSecondLoad.falseSuccessor();

              /*old End to delete 84*/
              EndNode endFalseSuccessorForLastPredicate = (EndNode) begFalseSuccessorForLastPredicate.next();

              /*283*/
              EndNode replaceEndFalseSuccessorForLastPredicate = graph.addWithoutUnique(new EndNode());
              begFalseSuccessorForLastPredicate.setNext(replaceEndFalseSuccessorForLastPredicate);

              /*old End to delete 91*/
              EndNode endTrueSuccessorForLastPredicate = (EndNode) loadForSum.next();

              /*289*/
              EndNode replaceEndTrueSuccessorForLastPredicate = graph.addWithoutUnique(new EndNode());
              loadForSum.setNext(null);
              begTrueSuccessorForLastPredicate.setNext(replaceEndTrueSuccessorForLastPredicate);
              loadForSum.safeDelete();

              /*282*/
              MergeNode mergeForInnerLoop = graph.add(new MergeNode());
              mergeForInnerLoop.addForwardEnd(endTrueSuccForSecondInnerLoopCondition);
              mergeForInnerLoop.addForwardEnd(replaceEndFalseSuccessorForLastPredicate);
              mergeForInnerLoop.addForwardEnd(replaceEndTrueSuccessorForLastPredicate);
              mergeForInnerLoop.setStateAfter(stateOfOperationLoop);

              /*293*/
              LoopEndNode endInnerLoop = graph.add(new LoopEndNode(beginUncompressedInnerLoop));
              mergeForInnerLoop.setNext(endInnerLoop);

              /*290*/
              ValuePhiNode sumAfterMergeForInnerLoop = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(64), mergeForInnerLoop)
              );
              sumAfterMergeForInnerLoop.addInput(sumForInnerLoop);
              sumAfterMergeForInnerLoop.addInput(sumForInnerLoop);
              sumAfterMergeForInnerLoop.addInput(addForSumValue);

              sumForInnerLoop.addInput(sumAfterMergeForInnerLoop);

              /*296*/
              EndNode endFalseSuccessorExitingInnerLoop = graph.addWithoutUnique(new EndNode());
              exitInnerLoop.setNext(endFalseSuccessorExitingInnerLoop);

              /*old 65*/
              MergeNode finalOperationLoop = (MergeNode) bindNodes.get(8);

              /*old 92*/
              ValuePhiNode sumAfterFinalMerge = null;
              for (Node n : finalOperationLoop.usages().snapshot()) {
                if (n instanceof ValuePhiNode) {
                  sumAfterFinalMerge = (ValuePhiNode) n;
                }
              }

              finalOperationLoop.removeEnd(endOldTrueSuccessorAfterFirstLoad);
              finalOperationLoop.removeEnd(endFalseSuccessorForLastPredicate);
              finalOperationLoop.removeEnd(endTrueSuccessorForLastPredicate);

              finalOperationLoop.addForwardEnd(endFalseSuccessorExitingInnerLoop);
              sumAfterFinalMerge.addInput(sendSumFromInnerLoop);

              // Need to delete the hanging EndNodes
              endOldTrueSuccessorAfterFirstLoad.safeDelete();
              endFalseSuccessorForLastPredicate.safeDelete();
              endTrueSuccessorForLastPredicate.safeDelete();

            }),
//            new PatternNode(new EndNode()),
            new AncestorNode(),
            new PatternNode(new LoopBeginNode()),
            new AncestorNode(),
            new PatternNode(new LoopBeginNode(), true),
            new PatternNode(new ArrayLengthNode(), true),
            new PatternNode(new IfNode()), new IndexNode(0),
            new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new IfNode()), new IndexNode(0),
            new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new IfNode()), new IndexNode(0),
            new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new IfNode()), new IndexNode(1),
            new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new IfNode()), new IndexNode(1),
            new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new AncestorNode(new LoopEndNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new EndNode()),
            new PatternNode(new MergeNode(), true),
//            new PatternNode(new InvokeNode()),// use it to stop the transformation
            new PatternNode(new LoopEndNode()));
        dataNode = null;
        lambdaCall = null;
        firstTime = true;
        bindNodes.clear();
      }
      assert GraphOrder.assertSchedulableGraph(graph);
      suites.getSuperHighTier().apply(graph, superHighTierContext);
      graph.maybeCompress();
      debug.dump(DebugContext.BASIC_LEVEL, graph, "After Super High tier");

      suites.getHighTier().apply(graph, highTierContext);
      graph.maybeCompress();
      debug.dump(DebugContext.BASIC_LEVEL, graph, "After high tier");

//      *{context.beforeLoopNode = thisnode}/Loop/ArrayAccess{thisnode.someattribute=context.beforeLoop}

      MidTierContext midTierContext = new MidTierContext(providers, target, optimisticOpts, profilingInfo);
      suites.getMidTier().apply(graph, midTierContext);
      graph.maybeCompress();
      debug.dump(DebugContext.BASIC_LEVEL, graph, "After mid tier");

      LowTierContext lowTierContext = new LowTierContext(providers, target);
      suites.getLowTier().apply(graph, lowTierContext);
      debug.dump(DebugContext.BASIC_LEVEL, graph, "After low tier");

      debug.dump(DebugContext.BASIC_LEVEL, graph.getLastSchedule(), "Final HIR schedule");
      graph.logInliningTree();
    } catch (Throwable e) {
      throw debug.handle(e);
    } finally {
      graph.checkCancellation();
    }
  }

  /*
   * This function creates a block of nodes to give the next
   * compressed value to the phi nodes based on the code
   *  if (!hasFinishedArray && startPosition[iterPointer + 1] == minNextIterator) {
   *     iterPointer++;
   *     nextValue = compressedRun[iterPointer];
   *   }
   */
  public static FixedWithNextNode fetchTheNextCompressedValue(StructuredGraph graph,
                                                              FrameState state,
                                                              ConstantNode constant0,
                                                              FixedWithNextNode connectWithPreviousGraph,
                                                              ValuePhiNode finishedArrayBoolean, Node[] compressedArrayRunAndPos,
                                                              AddNode increaseArrayPointer,
                                                              ValuePhiNode minIteratorFromLastUpdatedMerge,
                                                              ValuePhiNode iterationPointers,
                                                              ValuePhiNode nextArrayValues,
                                                              ValuePhiNode currentArrayValues) {
    /*195*//*212*/
    IntegerEqualsNode conditionHasFinishedFirArray = graph.addOrUnique(new IntegerEqualsNode(finishedArrayBoolean, constant0));

    BeginNode begFalseHasFinishedFirArray = graph.add(new BeginNode());
    BeginNode begTrueHasFinishedFirArray = graph.add(new BeginNode());

    IfNode hasFinishedFirArrayCheck = graph.add(new IfNode(conditionHasFinishedFirArray, begTrueHasFinishedFirArray, begFalseHasFinishedFirArray, 0.9));
    connectWithPreviousGraph.setNext(hasFinishedFirArrayCheck);

    /*199*//*216*/
    LoadIndexedNode loadFirArrNextPosForCondition = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayRunAndPos[1], increaseArrayPointer, null, JavaKind.Int));
    begTrueHasFinishedFirArray.setNext(loadFirArrNextPosForCondition);

    IntegerEqualsNode checkFirArrNextPosAndMinIter = graph.addOrUnique(new IntegerEqualsNode(minIteratorFromLastUpdatedMerge, loadFirArrNextPosForCondition));

    /*204*//*221*/
    BeginNode begTrueFirArrNextPosAndMinIter = graph.add(new BeginNode());
    BeginNode begFalseFirArrNextPosAndMinIter = graph.add(new BeginNode());

    IfNode firArrNextPosAndMinIterCondition = graph.add(new IfNode(checkFirArrNextPosAndMinIter, begTrueFirArrNextPosAndMinIter, begFalseFirArrNextPosAndMinIter, 0.9));
    loadFirArrNextPosForCondition.setNext(firArrNextPosAndMinIterCondition);

    /*207*//*224*/
    LoadIndexedNode loadFirRunArrForAssignment = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayRunAndPos[0], increaseArrayPointer, null, JavaKind.Int));
    begTrueFirArrNextPosAndMinIter.setNext(loadFirRunArrForAssignment);

    /*201*//*218*/
    EndNode endFalseHasFinishedFirArray = graph.addWithoutUnique(new EndNode());
    begFalseHasFinishedFirArray.setNext(endFalseHasFinishedFirArray);

    /*203*//*220*/
    EndNode endFalseFirArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
    begFalseFirArrNextPosAndMinIter.setNext(endFalseFirArrNextPosAndMinIter);

    /*208*//*225*/
    EndNode endTrueFirArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
    loadFirRunArrForAssignment.setNext(endTrueFirArrNextPosAndMinIter);

    /*202*//*219*/
    MergeNode mergeFirArrayNextRunAssignment = graph.add(new MergeNode());
    mergeFirArrayNextRunAssignment.addForwardEnd(endFalseHasFinishedFirArray);
    mergeFirArrayNextRunAssignment.addForwardEnd(endFalseFirArrNextPosAndMinIter);
    mergeFirArrayNextRunAssignment.addForwardEnd(endTrueFirArrNextPosAndMinIter);
    mergeFirArrayNextRunAssignment.setStateAfter(state);

    /*209*//*226*/
    ValuePhiNode iterationPointerForFirArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
        new ValuePhiNode(StampFactory.forInteger(32), mergeFirArrayNextRunAssignment)
    );
    iterationPointerForFirArrayAfterNextRunAssignmentMerge.addInput(iterationPointers);
    iterationPointerForFirArrayAfterNextRunAssignmentMerge.addInput(iterationPointers);
    iterationPointerForFirArrayAfterNextRunAssignmentMerge.addInput(increaseArrayPointer);

    iterationPointers.addInput(iterationPointerForFirArrayAfterNextRunAssignmentMerge);

    /*210*//*227*/
    ValuePhiNode nextValForFirArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
        new ValuePhiNode(StampFactory.forInteger(32), mergeFirArrayNextRunAssignment)
    );
    nextValForFirArrayAfterNextRunAssignmentMerge.addInput(nextArrayValues);
    nextValForFirArrayAfterNextRunAssignmentMerge.addInput(nextArrayValues);
    nextValForFirArrayAfterNextRunAssignmentMerge.addInput(loadFirRunArrForAssignment);

    currentArrayValues.addInput(nextValForFirArrayAfterNextRunAssignmentMerge);
    nextArrayValues.addInput(nextValForFirArrayAfterNextRunAssignmentMerge);

    return mergeFirArrayNextRunAssignment;
  }

  /*
   * This function takes the loadIndex in a predicate and removes it
   * replacing the condition in the predicate with the alignment run value
   *
   * The process followed in this function is:
   * 1) Fetch the LoadIndexedNode from the pattern
   * 2) Store the predecessor (begin) and next (if) nodes
   * 3) Fetch the condition node from the LoadIndexed Usages
   * 4) create a new condition node with the old constant and the new comparison
   * 5) replaceAtUsagesAndSafeDelete() old condition node with the new
   * 6) setNext() of LoadIndexed to null
   * 7) setNext() of predecessor the next node
   * 8) safeDelete() the LoadIndexed node
   */
  public static void replaceTheLoadIndexed(StructuredGraph graph,
                                           LoadIndexedNode loadPredicateToBeDeleted,
                                           ValuePhiNode currentValFromArray,
                                           FixedWithNextNode beforeNode) {

    IfNode secondPredicateCheck = (IfNode) loadPredicateToBeDeleted.next();

    IntegerLessThanNode secondPredicateCondition = null;
    for (Node n : loadPredicateToBeDeleted.usages().snapshot()) {
      if (n instanceof IntegerLessThanNode) {
        secondPredicateCondition = (IntegerLessThanNode) n;
      }
    }

    IntegerLessThanNode replaceSecondPredicateCondition = graph.addOrUnique(new IntegerLessThanNode(currentValFromArray, secondPredicateCondition.getY()));
    secondPredicateCondition.replaceAtUsagesAndDelete(replaceSecondPredicateCondition);

    loadPredicateToBeDeleted.setNext(null);
    beforeNode.setNext(secondPredicateCheck);
    loadPredicateToBeDeleted.safeDelete();
  }


  /*
   * A function to create compression loop nodes and connect them to the graph
   * It returns an array of nodes that are needed for future references
   * [0]: A NewArrayNode which consists the RLE compressed array with the run values
   * [1]: A NewArrayNode which consists the RLE-modification compressed array with the start position of the values
   * [2]: A ValueProxyNode which contains the last array index (aka the length of the compressed array)
   * [3]: The last node of the block to connect the rest of the graph
   */
  public static Node[] createCompressedArrayTransformation(StructuredGraph graph,
                                                           ResolvedJavaType elementType,
                                                           FrameState st,
                                                           FixedWithNextNode toConnectWithGraph,
                                                           ValueNode initialArray,
                                                           ConstantNode constantMinus1,
                                                           ConstantNode constant0,
                                                           ConstantNode constant1) {
    ArrayLengthNode alForRuns = graph.add(new ArrayLengthNode(initialArray));
    toConnectWithGraph.setNext(alForRuns);

    NewArrayNode runsArray = graph.addWithoutUnique(new NewArrayNode(elementType, alForRuns, true));
    alForRuns.setNext(runsArray);

    ArrayLengthNode alForStarPositions = graph.add(new ArrayLengthNode(initialArray));
    runsArray.setNext(alForStarPositions);

    NewArrayNode startPositionsArray = graph.addWithoutUnique(new NewArrayNode(elementType, alForStarPositions, true));
    alForStarPositions.setNext(startPositionsArray);

    LoadIndexedNode liShip0 = graph.add(new LoadIndexedNode(null, initialArray, constant0, null, JavaKind.Int));
    startPositionsArray.setNext(liShip0);

    StoreIndexedNode storeRunsFirstVal = graph.add(new StoreIndexedNode(runsArray,
        constant0,
        null,
        null,
        JavaKind.Int,
        liShip0));
    liShip0.setNext(storeRunsFirstVal);

    StoreIndexedNode storeLengthsFirstVal = graph.add(new StoreIndexedNode(startPositionsArray,
        constant0,
        null,
        null,
        JavaKind.Int,
        constant0));
    storeRunsFirstVal.setNext(storeLengthsFirstVal);
    storeRunsFirstVal.setStateAfter(st);

    EndNode endBeforeCompressionLoop = graph.addWithoutUnique(new EndNode());
    storeLengthsFirstVal.setNext(endBeforeCompressionLoop);
    storeLengthsFirstVal.setStateAfter(st);

    LoopBeginNode beginCompressionLoop = graph.add(new LoopBeginNode());
    beginCompressionLoop.addForwardEnd(endBeforeCompressionLoop);
    beginCompressionLoop.setStateAfter(st);

    //loop duration
    ArrayLengthNode alForIteration = graph.add(new ArrayLengthNode(initialArray));
    beginCompressionLoop.setNext(alForIteration);

    //iteration variable
    ValuePhiNode iterationVar = graph.addWithoutUnique(
        new ValuePhiNode(StampFactory.forInteger(32), beginCompressionLoop)
    );

    AddNode inputVarIncrement = graph.addWithoutUnique(new AddNode(iterationVar, constant1));

    iterationVar.addInput(constant1);
    iterationVar.addInput(inputVarIncrement);

    AddNode indexMinusForArrayComparison = graph.addWithoutUnique(new AddNode(iterationVar, constantMinus1));
    IntegerLessThanNode lessThanArrayLength = graph.addWithoutUnique(new IntegerLessThanNode(iterationVar, alForIteration));

    BeginNode startOfComparison = graph.add(new BeginNode());
    LoopExitNode exitComparison = graph.add(new LoopExitNode(beginCompressionLoop));
    exitComparison.setStateAfter(st);

    IfNode loopCondition = graph.add(new IfNode(lessThanArrayLength, startOfComparison, exitComparison, 0.9));

    alForIteration.setNext(loopCondition);

    //continue with the inner loop process
    LoadIndexedNode loadCurrentValue = graph.add(new LoadIndexedNode(null, initialArray, iterationVar, null, JavaKind.Int));
    startOfComparison.setNext(loadCurrentValue);

    LoadIndexedNode loadPreviousValue = graph.add(new LoadIndexedNode(null, initialArray, indexMinusForArrayComparison, null, JavaKind.Int));
    loadCurrentValue.setNext(loadPreviousValue);

    //load values for comparison
    IntegerEqualsNode checkConsecutiveValues = graph.addOrUnique(new IntegerEqualsNode(loadCurrentValue, loadPreviousValue));
    BeginNode ccvFalseSuccessor = graph.add(new BeginNode());
    BeginNode ccvTrueSuccessor = graph.add(new BeginNode());

    //check if two consecutive values are different
    IfNode consecutiveValuesComparison = graph.add(new IfNode(checkConsecutiveValues, ccvTrueSuccessor, ccvFalseSuccessor, 0.7));

    loadPreviousValue.setNext(consecutiveValuesComparison);

    EndNode endCcvTrueSuccessor = graph.addWithoutUnique(new EndNode());
    ccvTrueSuccessor.setNext(endCcvTrueSuccessor);

    LoadIndexedNode readNewStoringValue = graph.add(new LoadIndexedNode(null, initialArray, iterationVar, null, JavaKind.Int));
    ccvFalseSuccessor.setNext(readNewStoringValue);

    ValuePhiNode compArrayIndex = graph.addWithoutUnique(
        new ValuePhiNode(StampFactory.forInteger(32), beginCompressionLoop)
    );
    compArrayIndex.addInput(constant1);
    //The inputs will come later after initialising the input nodes

    StoreIndexedNode storeNewRunsValue = graph.add(new StoreIndexedNode(runsArray,
        compArrayIndex,
        null,
        null,
        JavaKind.Int,
        readNewStoringValue));
    readNewStoringValue.setNext(storeNewRunsValue);
    storeNewRunsValue.setStateAfter(st);

    StoreIndexedNode storeNewRunsLength = graph.add(new StoreIndexedNode(startPositionsArray,
        compArrayIndex,
        null,
        null,
        JavaKind.Int,
        iterationVar));
    storeNewRunsValue.setNext(storeNewRunsLength);
    storeNewRunsLength.setStateAfter(st);

    EndNode endCcvFalseSuccessor = graph.addWithoutUnique(new EndNode());
    storeNewRunsLength.setNext(endCcvFalseSuccessor);

    MergeNode mergeSuccessors = graph.add(new MergeNode());
    mergeSuccessors.addForwardEnd(endCcvTrueSuccessor);
    mergeSuccessors.addForwardEnd(endCcvFalseSuccessor);
    mergeSuccessors.setStateAfter(st);

    AddNode compIndexIncrement = graph.addWithoutUnique(new AddNode(compArrayIndex, constant1));

    ValuePhiNode compIndexForMerge = graph.addWithoutUnique(
        new ValuePhiNode(StampFactory.forInteger(32), mergeSuccessors)
    );
    compIndexForMerge.addInput(compArrayIndex);
    compIndexForMerge.addInput(compIndexIncrement);

    // Add the inputs of the phi node above after implementing the new nodes
    compArrayIndex.addInput(compIndexForMerge);

    LoopEndNode endCompressionLoop = graph.add(new LoopEndNode(beginCompressionLoop));

    // Connect the compression Loop with the begin of the processing loop
    mergeSuccessors.setNext(endCompressionLoop);

    ValueProxyNode sendCompressedLength = graph.addOrUnique(new ValueProxyNode(compArrayIndex, exitComparison));

    //exit to array operation
    ArrayLengthNode alForLastStartPos = graph.add(new ArrayLengthNode(initialArray));
    exitComparison.setNext(alForLastStartPos);

    StoreIndexedNode storeLastPosition = graph.add(new StoreIndexedNode(startPositionsArray,
        sendCompressedLength,
        null,
        null,
        JavaKind.Int,
        alForLastStartPos));
    alForLastStartPos.setNext(storeLastPosition);
    storeLastPosition.setStateAfter(st);

    return new Node[]{runsArray, startPositionsArray, sendCompressedLength, storeLastPosition};
  }

  public static class PatternNode {
    public Node currentNode;
    // 0 for true successor, 1 for false successor, 2 for both
    public int children;
    LambdaFunction lambda = null;
    boolean bindNode = false;

    PatternNode() {
    }

    PatternNode(Node node) {
      this.currentNode = node;
    }

    PatternNode(Node node, boolean bnd) {
      this.currentNode = node;
      this.bindNode = bnd;
    }

    PatternNode(Node node, LambdaFunction lbd) {
      this.currentNode = node;
      this.lambda = lbd;
    }

    PatternNode(Node node, int amountOfChildren) {
      this.currentNode = node;
      this.children = amountOfChildren;
    }

    @Override
    public boolean equals(Object o) {
      return this.currentNode.getClass().equals(o);
    }
  }

  public static class IndexNode extends PatternNode {
    public int index; // return all children in case of IfNode

    public IndexNode(int currentIndex) {
      this.index = currentIndex;
    }

    @Override
    public boolean equals(Object o) {
      return false;
    }
  }

  public static class AnyPatternNode extends PatternNode {
    public Node currentNode = null;
    LambdaFunction lambda = null;
    public Node avoidNode = null;

    AnyPatternNode() {
    }

    AnyPatternNode(LambdaFunction lbd) {
      super(null, lbd);
      this.lambda = lbd;
    }

    AnyPatternNode(Node avdnd, LambdaFunction lbd) {
      super(null, lbd);
      this.avoidNode = avdnd;
      this.lambda = lbd;
    }


    @Override
    public boolean equals(Object o) {
      if (this.avoidNode != null && this.avoidNode.getClass().equals(o)) {
        return false;
      }
      return true;
    }
  }

  public static class AncestorNode extends PatternNode {
    public Node currentNode = null;
    //Give max two nodes to avoid
    //better than using an arraylist
    //and looping through it every time
    public Node avoidNode = null;
    public Node secondAvoidNode = null;

    AncestorNode() {
    }

    AncestorNode(Node avdnd) {
      this.avoidNode = avdnd;
    }

    AncestorNode(Node avdnd, Node scavdnd) {
      this.avoidNode = avdnd;
      this.secondAvoidNode = scavdnd;
    }

    @Override
    public boolean equals(Object o) {
      if ((this.avoidNode != null && this.avoidNode.getClass().equals(o)) ||
          this.secondAvoidNode != null && this.secondAvoidNode.getClass().equals(o)) {
        return false;
      }
      return true;
    }
  }

  public static ArrayList<PatternNode[]> getNewPattern(PatternNode[] currentPattern, Node nextNode) {
    ArrayList<PatternNode[]> returnList = new ArrayList<>();
    if (!(currentPattern[0] instanceof AncestorNode)) {
      int newPatternLength = currentPattern.length - 1;
      PatternNode[] newPattern = new PatternNode[newPatternLength];
      System.arraycopy(currentPattern, 1, newPattern, 0, newPatternLength);
      returnList.add(newPattern);
      return returnList;
    } else if (currentPattern[1].equals(nextNode.getClass())) {
      int newPatternLength = currentPattern.length - 1;
      PatternNode[] newPattern = new PatternNode[newPatternLength];
      System.arraycopy(currentPattern, 1, newPattern, 0, newPatternLength);
      returnList.add(newPattern);
      returnList.add(currentPattern);
      return returnList;
    } else {
      returnList.add(currentPattern);
      return returnList;
    }
  }

  public static ArrayList<Node> getNext(Node currentNode) {
    ArrayList<Node> result = new ArrayList<>();

    if (currentNode instanceof FixedWithNextNode) {
      result.add(((FixedWithNextNode) currentNode).next());
    } else if (currentNode instanceof IfNode) {
      result.add(((IfNode) currentNode).trueSuccessor());
      result.add(((IfNode) currentNode).falseSuccessor());
    } else if (currentNode instanceof EndNode
        || currentNode instanceof OSRLocalNode
        || currentNode instanceof InstanceOfNode) {
      for (Node node : currentNode.usages()) {
        result.add(node);
      }
    }
    return result;
  }

  public static void matchSecond(Node incomingMatch, PatternNode... pattern) {

    if (pattern[0].lambda != null) {
      lambdaCall = pattern[0].lambda;
      dataNode = incomingMatch;
    }

    if (pattern.length == 0) {
      System.out.println("no pattern provided");
      return;
    }
    if (!(pattern[0].equals(incomingMatch.getClass()))) {
//      System.out.println("no match");
      return;
    } else {
      // Add the incoming match in the bind nodes
      if (pattern[0].bindNode) {
        bindNodes.add(incomingMatch);
      }
      if (pattern.length > 1) {
        if (pattern.length > 2 && pattern[1] instanceof IndexNode) {
          Node next = getNext(incomingMatch).get(((IndexNode) pattern[1]).index);
          // Assuming that Index will never be after an Ancestor!!
          matchSecond(next, getNewPattern(getNewPattern(pattern, next).get(0), next).get(0));
        }

        for (Node next : getNext(incomingMatch)) {
          if (next != null) {
            for (PatternNode[] ptn : getNewPattern(pattern, next)) {
              matchSecond(next, ptn);
            }
          }
        }
      } else {
        System.out.println("match");
        if (firstTime) {
          lambdaCall.simplePrint(dataNode);
          firstTime = false;
        }
        return;
      }
    }
  }
}

interface LambdaFunction {
  void simplePrint(Node node);
}