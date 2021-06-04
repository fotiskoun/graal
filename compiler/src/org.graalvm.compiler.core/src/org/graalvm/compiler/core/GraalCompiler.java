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

import jdk.vm.ci.code.BytecodeFrame;
import jdk.vm.ci.meta.JavaConstant;
import jdk.vm.ci.meta.JavaKind;
import jdk.vm.ci.meta.ResolvedJavaType;
import org.graalvm.compiler.bytecode.Bytecode;
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
import org.graalvm.compiler.java.GraphBuilderPhase;
import org.graalvm.compiler.lir.asm.CompilationResultBuilderFactory;
import org.graalvm.compiler.lir.phases.LIRSuites;
import org.graalvm.compiler.nodes.AbstractBeginNode;
import org.graalvm.compiler.nodes.BeginNode;
import org.graalvm.compiler.nodes.ConstantNode;
import org.graalvm.compiler.nodes.EndNode;
import org.graalvm.compiler.nodes.FixedGuardNode;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.FrameState;
import org.graalvm.compiler.nodes.IfNode;
import org.graalvm.compiler.nodes.Invoke;
import org.graalvm.compiler.nodes.InvokeNode;
import org.graalvm.compiler.nodes.LogicNode;
import org.graalvm.compiler.nodes.LoopBeginNode;
import org.graalvm.compiler.nodes.LoopEndNode;
import org.graalvm.compiler.nodes.LoopExitNode;
import org.graalvm.compiler.nodes.MergeNode;
import org.graalvm.compiler.nodes.NodeView;
import org.graalvm.compiler.nodes.ParameterNode;
import org.graalvm.compiler.nodes.StartNode;
import org.graalvm.compiler.nodes.StateSplit;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.ValueNode;
import org.graalvm.compiler.nodes.ValuePhiNode;
import org.graalvm.compiler.nodes.ValueProxyNode;
import org.graalvm.compiler.nodes.calc.AddNode;
import org.graalvm.compiler.nodes.calc.IntegerEqualsNode;
import org.graalvm.compiler.nodes.calc.IntegerLessThanNode;
import org.graalvm.compiler.nodes.calc.MulNode;
import org.graalvm.compiler.nodes.calc.RightShiftNode;
import org.graalvm.compiler.nodes.calc.SignExtendNode;
import org.graalvm.compiler.nodes.calc.SubNode;
import org.graalvm.compiler.nodes.calc.UnsignedRightShiftNode;
import org.graalvm.compiler.nodes.extended.OSRLocalNode;
import org.graalvm.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import org.graalvm.compiler.nodes.graphbuilderconf.IntrinsicContext;
import org.graalvm.compiler.nodes.java.ArrayLengthNode;
import org.graalvm.compiler.nodes.java.InstanceOfNode;
import org.graalvm.compiler.nodes.java.LoadIndexedNode;
import org.graalvm.compiler.nodes.java.NewArrayNode;
import org.graalvm.compiler.nodes.java.StoreIndexedNode;
import org.graalvm.compiler.phases.OptimisticOptimizations;
import org.graalvm.compiler.phases.PhaseSuite;
import org.graalvm.compiler.phases.common.DeadCodeEliminationPhase;
import org.graalvm.compiler.phases.common.inlining.InliningUtil;
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

import static jdk.vm.ci.meta.DeoptimizationAction.InvalidateReprofile;
import static jdk.vm.ci.meta.DeoptimizationAction.None;
import static jdk.vm.ci.meta.DeoptimizationReason.TransferToInterpreter;
import static jdk.vm.ci.meta.DeoptimizationReason.UnreachedCode;
import static org.graalvm.compiler.nodes.ConstantNode.getConstantNodes;
import static org.graalvm.compiler.nodes.graphbuilderconf.IntrinsicContext.CompilationContext.INLINE_AFTER_PARSING;

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
              EndNode endBeforeLoop = (EndNode) ((FixedWithNextNode) x).next();

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
              for (int arrayId = 0; arrayId < numberOfArrays; arrayId++) {
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

              for (int compressEachArray = 0; compressEachArray < numberOfArrays; compressEachArray++) {
                compressedArrayNodes[compressEachArray] = createCompressedArrayTransformation(graph, elementType,
                    st, nodesToConnectCompressionLoopWithGraph[compressEachArray], uncompressedArrayNodes[compressEachArray], constantMinus1, constant0, constant1);
                //store the array you got to connect the next loop
                nodesToConnectCompressionLoopWithGraph[compressEachArray + 1] = (FixedWithNextNode) compressedArrayNodes[compressEachArray][3];
              }
              //Node numbers returned from the function inside the for loop above
              /*16*//*18*//*34*//*61*/
              /*64*//*66*//*82*//*108*/

              LoadIndexedNode[][] loadValuesArraysForNextAndCurrent = new LoadIndexedNode[2][2];
              FixedWithNextNode previousNodeOfGraphConnectedWithLoadIndBlock = (StoreIndexedNode) compressedArrayNodes[1][3];

              for(int fetchedAllArraysLoad = 0; fetchedAllArraysLoad < totalTimesToFetchLoadIndexed; fetchedAllArraysLoad++){
                for(int arrayFetched = 0; arrayFetched <numberOfArrays; arrayFetched++){
                  loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched] = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[arrayFetched][0], constant0, null, JavaKind.Int));
                  previousNodeOfGraphConnectedWithLoadIndBlock.setNext(loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched]);
                  previousNodeOfGraphConnectedWithLoadIndBlock = loadValuesArraysForNextAndCurrent[fetchedAllArraysLoad][arrayFetched];
                }
              }
//
//              /*111*/
//       0 1o       LoadIndexedNode loadFirstValFirstArrayForCurrent = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][0], constant0, null, JavaKind.Int));
//              ((StoreIndexedNode) compressedArrayNodes[1][3]).setNext(loadFirstValFirstArrayForCurrent);
//
//     0 0o         LoadIndexedNode loadFirstValSecondArrayForCurrent = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][0], constant0, null, JavaKind.Int));
//              loadFirstValFirstArrayForCurrent.setNext(loadFirstValSecondArrayForCurrent);
//
//        1 1o    //TODO: check for optimizations by using the same array node in 1st and 3rd LoadIndexed
//              LoadIndexedNode loadFirstValFirstArrayForNext = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][0], constant0, null, JavaKind.Int));
//              loadFirstValSecondArrayForCurrent.setNext(loadFirstValFirstArrayForNext);
//
//         1 0o     LoadIndexedNode loadFirstValSecondArrayForNext = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][0], constant0, null, JavaKind.Int));
//              loadFirstValFirstArrayForNext.setNext(loadFirstValSecondArrayForNext);

              // TODO : h seira einai olo to gamhsi! Sto grafo pou 8a kaneis thn allagh gia to if, kane thn allagh kai sth seira, den 8a allaksei polla logika

              loadValuesArraysForNextAndCurrent[totalTimesToFetchLoadIndexed-1][numberOfArrays-1].setNext(endBeforeLoop);

              /*117*/
              LoopBeginNode operationLoopBegNode = (LoopBeginNode) bindNodes.get(0);
              FrameState stateOfOperationLoop = operationLoopBegNode.stateAfter().duplicate();

              /*119*/
              ValuePhiNode iterationPointerForSecondArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              iterationPointerForSecondArray.addInput(constant0);

              /*120*/
              ValuePhiNode iterationPointerForFirstArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              iterationPointerForFirstArray.addInput(constant0);

              /*121*/
              ValuePhiNode currentValForSecondArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              currentValForSecondArray.addInput(loadValuesArraysForNextAndCurrent[0][1]);

              /*122*/
              ValuePhiNode currentValForFirstArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              currentValForFirstArray.addInput(loadValuesArraysForNextAndCurrent[0][0]);

              /*123*/
              ValuePhiNode nextValForSecondArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              nextValForSecondArray.addInput(loadValuesArraysForNextAndCurrent[1][1]);

              /*124*/
              ValuePhiNode nextValForFirstArray = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              nextValForFirstArray.addInput(loadValuesArraysForNextAndCurrent[1][0]);

              /*125*/
              ValuePhiNode currentIteratorVal = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              currentIteratorVal.addInput(constant0);

              /*126*/
              ValuePhiNode nextMinIteratorVal = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), operationLoopBegNode)
              );
              nextMinIteratorVal.addInput(constantMinus1);

              /* old 31 TODO: to be deleted*/
              LoadIndexedNode loadForFirstPredicateToBeDeleted = (LoadIndexedNode) bindNodes.get(2);

              /*144*/
              BeginNode startTheOperationLoop = (BeginNode) loadForFirstPredicateToBeDeleted.predecessor();

              /*146*/
              IntegerEqualsNode conditionToCalculateMinIteratorSecondArray = graph.addOrUnique(new IntegerEqualsNode((ValueProxyNode) compressedArrayNodes[1][2], iterationPointerForSecondArray));

              BeginNode begFalseSuccCalculatingMinIterSecondArray = graph.add(new BeginNode());
              BeginNode begTrueSuccCalculatingMinIterSecondArray = graph.add(new BeginNode());

              IfNode minIteratorSecondArrayCondition = graph.add(new IfNode(conditionToCalculateMinIteratorSecondArray, begTrueSuccCalculatingMinIterSecondArray, begFalseSuccCalculatingMinIterSecondArray, 0.1));
              startTheOperationLoop.setNext(minIteratorSecondArrayCondition);

              AddNode increaseSecondArrIterPointer = graph.addWithoutUnique(new AddNode(iterationPointerForSecondArray, constant1));

              /*151*/
              LoadIndexedNode loadSecondArrayNextStartPos = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][1], increaseSecondArrIterPointer, null, JavaKind.Int));
              begFalseSuccCalculatingMinIterSecondArray.setNext(loadSecondArrayNextStartPos);

              /*152*/
              EndNode endTrueSuccessorCalculatingMinIterSecondArr = graph.addWithoutUnique(new EndNode());
              begTrueSuccCalculatingMinIterSecondArray.setNext(endTrueSuccessorCalculatingMinIterSecondArr);

              /*154*/
              EndNode endFalseSuccessorCalculatingMinIterSecondArr = graph.addWithoutUnique(new EndNode());
              loadSecondArrayNextStartPos.setNext(endFalseSuccessorCalculatingMinIterSecondArr);

              /*153*/
              MergeNode mergeCalculatingMinIterSecondArraySuccessors = graph.add(new MergeNode());
              mergeCalculatingMinIterSecondArraySuccessors.addForwardEnd(endTrueSuccessorCalculatingMinIterSecondArr);
              mergeCalculatingMinIterSecondArraySuccessors.addForwardEnd(endFalseSuccessorCalculatingMinIterSecondArr);
              mergeCalculatingMinIterSecondArraySuccessors.setStateAfter(stateOfOperationLoop);

              /*155*/
              ValuePhiNode nextMinIteratorValForSecondArrayMergeCalc = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeCalculatingMinIterSecondArraySuccessors)
              );
              nextMinIteratorValForSecondArrayMergeCalc.addInput(nextMinIteratorVal);
              nextMinIteratorValForSecondArrayMergeCalc.addInput(loadSecondArrayNextStartPos);

              /*156*/
              ValuePhiNode finishSecondArrayBoolean = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeCalculatingMinIterSecondArraySuccessors)
              );
              finishSecondArrayBoolean.addInput(constant1);
              finishSecondArrayBoolean.addInput(constant0);

              /*158*/
              IntegerEqualsNode conditionToCalculateMinIteratorFirstArray = graph.addOrUnique(new IntegerEqualsNode((ValueProxyNode) compressedArrayNodes[0][2], iterationPointerForFirstArray));

              BeginNode begFalseSuccCalculatingMinIterFirstArray = graph.add(new BeginNode());
              BeginNode begTrueSuccCalculatingMinIterFirstArray = graph.add(new BeginNode());

              IfNode minIteratorFirstArrayCondition = graph.add(new IfNode(conditionToCalculateMinIteratorFirstArray, begTrueSuccCalculatingMinIterFirstArray, begFalseSuccCalculatingMinIterFirstArray, 0.1));
              mergeCalculatingMinIterSecondArraySuccessors.setNext(minIteratorFirstArrayCondition);

              AddNode increaseFirstIterPointer = graph.addWithoutUnique(new AddNode(iterationPointerForFirstArray, constant1));

              /*163*/
              LoadIndexedNode loadFirstArrayNextStartPos = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][1], increaseFirstIterPointer, null, JavaKind.Int));
              begFalseSuccCalculatingMinIterFirstArray.setNext(loadFirstArrayNextStartPos);

              IntegerLessThanNode conditionFirstArrayStartPosAndMinIter = graph.addWithoutUnique(new IntegerLessThanNode(loadFirstArrayNextStartPos, nextMinIteratorValForSecondArrayMergeCalc));

              BeginNode begFalseSuccForFirstArrayStartAndMInIter = graph.add(new BeginNode());
              BeginNode begTrueSuccForFirstArrayStartAndMInIter = graph.add(new BeginNode());

              IfNode firstArrayStartAndMinIterCondition = graph.add(new IfNode(conditionFirstArrayStartPosAndMinIter, begTrueSuccForFirstArrayStartAndMInIter, begFalseSuccForFirstArrayStartAndMInIter, 0.5));
              loadFirstArrayNextStartPos.setNext(firstArrayStartAndMinIterCondition);

              /*168*/
              IntegerLessThanNode checkMinIteratorLessThanZero = graph.addWithoutUnique(new IntegerLessThanNode(nextMinIteratorValForSecondArrayMergeCalc, constant0));

              EndNode endTrueSuccCalculatingMinIterFirstArray = graph.addWithoutUnique(new EndNode());
              begTrueSuccCalculatingMinIterFirstArray.setNext(endTrueSuccCalculatingMinIterFirstArray);

              /*173*/
              EndNode endTrueSuccForFirstArrayStartAndMInIter = graph.addWithoutUnique(new EndNode());
              begTrueSuccForFirstArrayStartAndMInIter.setNext(endTrueSuccForFirstArrayStartAndMInIter);

              /*176*/
              BeginNode begTrueSuccForMinIterLessThanZero = graph.add(new BeginNode());
              BeginNode begFalseSuccForMinIterLessThanZero = graph.add(new BeginNode());

              IfNode minIterLessThanZeroCondition = graph.add(new IfNode(checkMinIteratorLessThanZero, begTrueSuccForMinIterLessThanZero, begFalseSuccForMinIterLessThanZero, 0.1));
              begFalseSuccForFirstArrayStartAndMInIter.setNext(minIterLessThanZeroCondition);

              /*171*/
              EndNode endFalseSuccForMinIterLessThanZero = graph.addWithoutUnique(new EndNode());
              begFalseSuccForMinIterLessThanZero.setNext(endFalseSuccForMinIterLessThanZero);
              /*175*/
              EndNode endTrueSuccForMinIterLessThanZero = graph.addWithoutUnique(new EndNode());
              begTrueSuccForMinIterLessThanZero.setNext(endTrueSuccForMinIterLessThanZero);

              /*174*/
              MergeNode FirstArrayStartMinIterAndMinIterLessThanZeroTrueAncestorsMerge = graph.add(new MergeNode());
              FirstArrayStartMinIterAndMinIterLessThanZeroTrueAncestorsMerge.addForwardEnd(endTrueSuccForFirstArrayStartAndMInIter);
              FirstArrayStartMinIterAndMinIterLessThanZeroTrueAncestorsMerge.addForwardEnd(endTrueSuccForMinIterLessThanZero);
              FirstArrayStartMinIterAndMinIterLessThanZeroTrueAncestorsMerge.setStateAfter(stateOfOperationLoop);

              /*180*/
              LoadIndexedNode firstArrayNextStartPosForAssignment = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][1], increaseFirstIterPointer, null, JavaKind.Int));
              FirstArrayStartMinIterAndMinIterLessThanZeroTrueAncestorsMerge.setNext(firstArrayNextStartPosForAssignment);

              EndNode endTrueSuccForMinIterLessThanZeroAfterMinIterAssignment = graph.addWithoutUnique(new EndNode());
              firstArrayNextStartPosForAssignment.setNext(endTrueSuccForMinIterLessThanZeroAfterMinIterAssignment);

              /*170*/
              MergeNode mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero = graph.add(new MergeNode());
              mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero.addForwardEnd(endTrueSuccCalculatingMinIterFirstArray);
              mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero.addForwardEnd(endFalseSuccForMinIterLessThanZero);
              mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero.addForwardEnd(endTrueSuccForMinIterLessThanZeroAfterMinIterAssignment);
              mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero.setStateAfter(stateOfOperationLoop);

              /*172*/
              ValuePhiNode finishedFirstArrayBooleanAfterFirstArrAndMinIterTotalMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero)
              );
              finishedFirstArrayBooleanAfterFirstArrAndMinIterTotalMerge.addInput(constant1);
              finishedFirstArrayBooleanAfterFirstArrAndMinIterTotalMerge.addInput(constant0);
              finishedFirstArrayBooleanAfterFirstArrAndMinIterTotalMerge.addInput(constant0);

              /*182*/
              ValuePhiNode minNextIterAfterFirstArrAndMinIterTotalMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero)
              );
              minNextIterAfterFirstArrAndMinIterTotalMerge.addInput(nextMinIteratorValForSecondArrayMergeCalc);
              minNextIterAfterFirstArrAndMinIterTotalMerge.addInput(nextMinIteratorValForSecondArrayMergeCalc);
              minNextIterAfterFirstArrAndMinIterTotalMerge.addInput(firstArrayNextStartPosForAssignment);

              currentIteratorVal.addInput(minNextIterAfterFirstArrAndMinIterTotalMerge);
              nextMinIteratorVal.addInput(minNextIterAfterFirstArrAndMinIterTotalMerge);

              /*184*/
              IntegerEqualsNode conditionHasFinishedSecondArray = graph.addOrUnique(new IntegerEqualsNode(finishSecondArrayBoolean, constant0));

              BeginNode begFalseHasFinishedSecondArray = graph.add(new BeginNode());
              BeginNode begTrueHasFinishedSecondArray = graph.add(new BeginNode());

              IfNode hasFinishedSecondArrayCheck = graph.add(new IfNode(conditionHasFinishedSecondArray, begTrueHasFinishedSecondArray, begFalseHasFinishedSecondArray, 0.1));
              mergeTotalFirstArrayStartMinIterAndMinIterLessThanZero.setNext(hasFinishedSecondArrayCheck);

              /*188*/
              LoadIndexedNode loadSecondArrNextPosForCondition = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][1], increaseSecondArrIterPointer, null, JavaKind.Int));
              begTrueHasFinishedSecondArray.setNext(loadSecondArrNextPosForCondition);

              IntegerEqualsNode checkSecondArrNextPosAndMinIter = graph.addOrUnique(new IntegerEqualsNode(minNextIterAfterFirstArrAndMinIterTotalMerge, loadSecondArrNextPosForCondition));

              /*193*/
              BeginNode begTrueSecondArrNextPosAndMinIter = graph.add(new BeginNode());
              BeginNode begFalseSecondArrNextPosAndMinIter = graph.add(new BeginNode());

              IfNode secondArrNextPosAndMinIterCondition = graph.add(new IfNode(checkSecondArrNextPosAndMinIter, begTrueSecondArrNextPosAndMinIter, begFalseSecondArrNextPosAndMinIter, 0.5));
              loadSecondArrNextPosForCondition.setNext(secondArrNextPosAndMinIterCondition);

              /*196*/
              LoadIndexedNode loadSecondRunArrForAssignment = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[1][0], increaseSecondArrIterPointer, null, JavaKind.Int));
              begTrueSecondArrNextPosAndMinIter.setNext(loadSecondRunArrForAssignment);

              EndNode endTrueSecondArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
              loadSecondRunArrForAssignment.setNext(endTrueSecondArrNextPosAndMinIter);

              /*192*/
              EndNode endFalseSecondArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
              begFalseSecondArrNextPosAndMinIter.setNext(endFalseSecondArrNextPosAndMinIter);

              /*190*/
              EndNode endFalseHasFinishedSecondArray = graph.addWithoutUnique(new EndNode());
              begFalseHasFinishedSecondArray.setNext(endFalseHasFinishedSecondArray);

              /*191*/
              MergeNode mergeSecondArrayNextRunAssignment = graph.add(new MergeNode());
              mergeSecondArrayNextRunAssignment.addForwardEnd(endFalseHasFinishedSecondArray);
              mergeSecondArrayNextRunAssignment.addForwardEnd(endFalseSecondArrNextPosAndMinIter);
              mergeSecondArrayNextRunAssignment.addForwardEnd(endTrueSecondArrNextPosAndMinIter);
              mergeSecondArrayNextRunAssignment.setStateAfter(stateOfOperationLoop);

              /*198*/
              ValuePhiNode iterationPointerForSecondArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeSecondArrayNextRunAssignment)
              );
              iterationPointerForSecondArrayAfterNextRunAssignmentMerge.addInput(iterationPointerForSecondArray);
              iterationPointerForSecondArrayAfterNextRunAssignmentMerge.addInput(iterationPointerForSecondArray);
              iterationPointerForSecondArrayAfterNextRunAssignmentMerge.addInput(increaseSecondArrIterPointer);

              iterationPointerForSecondArray.addInput(iterationPointerForSecondArrayAfterNextRunAssignmentMerge);

              /*199*/
              ValuePhiNode nextValForSecondArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeSecondArrayNextRunAssignment)
              );
              nextValForSecondArrayAfterNextRunAssignmentMerge.addInput(nextValForSecondArray);
              nextValForSecondArrayAfterNextRunAssignmentMerge.addInput(nextValForSecondArray);
              nextValForSecondArrayAfterNextRunAssignmentMerge.addInput(loadSecondRunArrForAssignment);

              currentValForSecondArray.addInput(nextValForSecondArrayAfterNextRunAssignmentMerge);
              nextValForSecondArray.addInput(nextValForSecondArrayAfterNextRunAssignmentMerge);

              /*201*/
              IntegerEqualsNode conditionHasFinishedFirstArray = graph.addOrUnique(new IntegerEqualsNode(finishedFirstArrayBooleanAfterFirstArrAndMinIterTotalMerge, constant0));

              BeginNode begFalseHasFinishedFirstArray = graph.add(new BeginNode());
              BeginNode begTrueHasFinishedFirstArray = graph.add(new BeginNode());

              IfNode hasFinishedFirstArrayCheck = graph.add(new IfNode(conditionHasFinishedFirstArray, begTrueHasFinishedFirstArray, begFalseHasFinishedFirstArray, 0.1));
              mergeSecondArrayNextRunAssignment.setNext(hasFinishedFirstArrayCheck);

              /*205*/
              LoadIndexedNode loadFirstArrNextPosForCondition = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][1], increaseFirstIterPointer, null, JavaKind.Int));
              begTrueHasFinishedFirstArray.setNext(loadFirstArrNextPosForCondition);

              IntegerEqualsNode checkFirstArrNextPosAndMinIter = graph.addOrUnique(new IntegerEqualsNode(minNextIterAfterFirstArrAndMinIterTotalMerge, loadFirstArrNextPosForCondition));

              /*210*/
              BeginNode begTrueFirstArrNextPosAndMinIter = graph.add(new BeginNode());
              BeginNode begFalseFirstArrNextPosAndMinIter = graph.add(new BeginNode());

              IfNode firstArrNextPosAndMinIterCondition = graph.add(new IfNode(checkFirstArrNextPosAndMinIter, begTrueFirstArrNextPosAndMinIter, begFalseFirstArrNextPosAndMinIter, 0.5));
              loadFirstArrNextPosForCondition.setNext(firstArrNextPosAndMinIterCondition);

              /*213*/
              LoadIndexedNode loadFirstRunArrForAssignment = graph.add(new LoadIndexedNode(null, (NewArrayNode) compressedArrayNodes[0][0], increaseFirstIterPointer, null, JavaKind.Int));
              begTrueFirstArrNextPosAndMinIter.setNext(loadFirstRunArrForAssignment);

              /*207*/
              EndNode endFalseHasFinishedFirstArray = graph.addWithoutUnique(new EndNode());
              begFalseHasFinishedFirstArray.setNext(endFalseHasFinishedFirstArray);

              /*209*/
              EndNode endFalseFirstArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
              begFalseFirstArrNextPosAndMinIter.setNext(endFalseFirstArrNextPosAndMinIter);

              /*214*/
              EndNode endTrueFirstArrNextPosAndMinIter = graph.addWithoutUnique(new EndNode());
              loadFirstRunArrForAssignment.setNext(endTrueFirstArrNextPosAndMinIter);

              /*208*/
              MergeNode mergeFirstArrayNextRunAssignment = graph.add(new MergeNode());
              mergeFirstArrayNextRunAssignment.addForwardEnd(endFalseHasFinishedFirstArray);
              mergeFirstArrayNextRunAssignment.addForwardEnd(endFalseFirstArrNextPosAndMinIter);
              mergeFirstArrayNextRunAssignment.addForwardEnd(endTrueFirstArrNextPosAndMinIter);
              mergeFirstArrayNextRunAssignment.setStateAfter(stateOfOperationLoop);

              /*215*/
              ValuePhiNode iterationPointerForFirstArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeFirstArrayNextRunAssignment)
              );
              iterationPointerForFirstArrayAfterNextRunAssignmentMerge.addInput(iterationPointerForFirstArray);
              iterationPointerForFirstArrayAfterNextRunAssignmentMerge.addInput(iterationPointerForFirstArray);
              iterationPointerForFirstArrayAfterNextRunAssignmentMerge.addInput(increaseFirstIterPointer);

              iterationPointerForFirstArray.addInput(iterationPointerForFirstArrayAfterNextRunAssignmentMerge);

              /*216*/
              ValuePhiNode nextValForFirstArrayAfterNextRunAssignmentMerge = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeFirstArrayNextRunAssignment)
              );
              nextValForFirstArrayAfterNextRunAssignmentMerge.addInput(nextValForFirstArray);
              nextValForFirstArrayAfterNextRunAssignmentMerge.addInput(nextValForFirstArray);
              nextValForFirstArrayAfterNextRunAssignmentMerge.addInput(loadFirstRunArrForAssignment);

              currentValForFirstArray.addInput(nextValForFirstArrayAfterNextRunAssignmentMerge);
              nextValForFirstArray.addInput(nextValForFirstArrayAfterNextRunAssignmentMerge);

              /*218*/
              IntegerEqualsNode conditionMinIterMinusOne = graph.addOrUnique(new IntegerEqualsNode(minNextIterAfterFirstArrAndMinIterTotalMerge, constantMinus1));

              BeginNode begFalseMinIterMinusOne = graph.add(new BeginNode());
              BeginNode begTrueMinIterMinusOne = graph.add(new BeginNode());

              IfNode MinIterMinusOneCheck = graph.add(new IfNode(conditionMinIterMinusOne, begTrueMinIterMinusOne, begFalseMinIterMinusOne, 0.1));
              mergeFirstArrayNextRunAssignment.setNext(MinIterMinusOneCheck);

              /*222*/
              ArrayLengthNode uncompArrayLengthForLastIteration = graph.add(new ArrayLengthNode(uncompressedArrayNodes[0]));
              begTrueMinIterMinusOne.setNext(uncompArrayLengthForLastIteration);

              SubNode lengthForLastPositionSubtraction = graph.addWithoutUnique(new SubNode(uncompArrayLengthForLastIteration, currentIteratorVal));

              /*225*/
              SubNode lengthFromMinIterSubtraction = graph.addWithoutUnique(new SubNode(minNextIterAfterFirstArrAndMinIterTotalMerge, currentIteratorVal));

              /*226*/
              EndNode endTrueMinIterMinusOne = graph.addWithoutUnique(new EndNode());
              uncompArrayLengthForLastIteration.setNext(endTrueMinIterMinusOne);
              /*228*/
              EndNode endFalseMinIterMinusOne = graph.addWithoutUnique(new EndNode());
              begFalseMinIterMinusOne.setNext(endFalseMinIterMinusOne);

              /*227*/
              MergeNode mergeForLength = graph.add(new MergeNode());
              mergeForLength.addForwardEnd(endTrueMinIterMinusOne);
              mergeForLength.addForwardEnd(endFalseMinIterMinusOne);
              mergeForLength.setStateAfter(stateOfOperationLoop);

              /*229*/
              ValuePhiNode lengthBetweenAlignments = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), mergeForLength)
              );
              lengthBetweenAlignments.addInput(lengthForLastPositionSubtraction);
              lengthBetweenAlignments.addInput(lengthFromMinIterSubtraction);


              // get the iterator increase (AddIntegerNode) to change the increasing value

              //Integer less than node which checks the insertion inside the operation loop
              /*130 old 23*/
              IntegerLessThanNode conditionArrayIterationComparison = null;
              for (Node n : alOfShip.usages().snapshot()) {
                if (n instanceof IntegerLessThanNode) {
                  conditionArrayIterationComparison = (IntegerLessThanNode) n;
                }
              }

              //Iterator of the Loop 127 old 20
              ValuePhiNode iteratorInOperationLoop = (ValuePhiNode) conditionArrayIterationComparison.getX();
              /*251 old 61*/
              AddNode iteratorIncrease = null;
              for (Node n : iteratorInOperationLoop.inputs().snapshot()) {
                if (n instanceof AddNode) {
                  iteratorIncrease = (AddNode) n;
                }
              }

              iteratorIncrease.setY(lengthBetweenAlignments);


              int numberOfPredicates = 3; // TODO: find a way to grab the predicates maybe from the pattern?

              LoadIndexedNode[] loadIndexedNodesFromPredicates = new LoadIndexedNode[]{
                  (LoadIndexedNode) bindNodes.get(2),
                  (LoadIndexedNode) bindNodes.get(3),
                  (LoadIndexedNode) bindNodes.get(4)
              };

              FixedWithNextNode[] connectWithPreviousGraph = new FixedWithNextNode[]{
                  mergeForLength,
                  (FixedWithNextNode) loadIndexedNodesFromPredicates[1].predecessor(),
                  (FixedWithNextNode) loadIndexedNodesFromPredicates[2].predecessor()
              };

              ValuePhiNode[] currentValuesForArrays = new ValuePhiNode[]{currentValForFirstArray, currentValForSecondArray};

              for (int loadInPredicate = 0; loadInPredicate < numberOfPredicates; loadInPredicate++) {
                int arrayAndLoadMatch = -1;
                for (int arrayInLoadIndexed = 0; arrayInLoadIndexed < numberOfArrays; arrayInLoadIndexed++) {
                  if (loadIndexedNodesFromPredicates[loadInPredicate].array().getId() == uncompressedArrayNodes[arrayInLoadIndexed].getId()) {
                    arrayAndLoadMatch = arrayInLoadIndexed;
                    break;
                  }
                }
                // Use this if in case a predicate does not come from a compressed array
                if (arrayAndLoadMatch>-1){
                  changeTheLoadIndexed(graph, loadIndexedNodesFromPredicates[loadInPredicate], currentValuesForArrays[arrayAndLoadMatch], connectWithPreviousGraph[loadInPredicate]);
                }
              }


              /*old 55*/
              LoadIndexedNode loadForSum = (LoadIndexedNode) bindNodes.get(5);

              BeginNode begFalseSuccForArraySum = (BeginNode) loadForSum.predecessor();
              EndNode endFalseSuccForArraySum = (EndNode) loadForSum.next();

              /*249 old 56*/
              SignExtendNode extendToFitSumLongVal = null;
              for (Node n : loadForSum.usages().snapshot()) {
                if (n instanceof SignExtendNode) {
                  extendToFitSumLongVal = (SignExtendNode) n;
                }
              }

              /*248*/
              SubNode runTimesLength = graph.addOrUnique(new SubNode(currentValForFirstArray, lengthBetweenAlignments));

              extendToFitSumLongVal.setValue(runTimesLength);

              loadForSum.setNext(null);
              begFalseSuccForArraySum.setNext(endFalseSuccForArraySum);
              loadForSum.safeDelete();

              // TODO: Check the Phis and merges

            }),
            new PatternNode(new EndNode()),
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
            new AncestorNode(new LoopEndNode()),
            new PatternNode(new LoadIndexedNode(), true),
            new PatternNode(new EndNode()),
            new PatternNode(new MergeNode()),
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
  public static void changeTheLoadIndexed(StructuredGraph graph,
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
      System.out.println("no match");
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