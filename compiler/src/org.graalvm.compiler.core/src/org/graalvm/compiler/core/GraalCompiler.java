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
            new PatternNode(new InvokeNode(), (x) -> {
              // Duplicate the frame
              // Need to find the best generic class for the stateAfter
              Node nodeIncludingFrameState = x;
              while(!(nodeIncludingFrameState instanceof  StateSplit)){
                nodeIncludingFrameState = x.predecessor();
              }


              FrameState st = ((StateSplit) nodeIncludingFrameState).stateAfter().duplicate();
              //Keep the connection between start and end node
              EndNode endBeforeLoop = (EndNode) ((FixedWithNextNode) x).next();

              ArrayLengthNode alOfShip = (ArrayLengthNode) bindNodes.get(1);
              ValueNode toBeCompressedArray = ((StoreIndexedNode) x.predecessor()).value();


              ArrayLengthNode alForRuns = graph.add(new ArrayLengthNode(toBeCompressedArray));
              ((FixedWithNextNode) x).setNext(alForRuns);

              ResolvedJavaType elementType = providers.getMetaAccess().lookupJavaType(Integer.TYPE);

              NewArrayNode runsArray = graph.addWithoutUnique(new NewArrayNode(elementType, alForRuns, true));
              alForRuns.setNext(runsArray);

              /*5*/
              ArrayLengthNode alForStarPositions = graph.add(new ArrayLengthNode(toBeCompressedArray));
              runsArray.setNext(alForStarPositions);

              NewArrayNode startPositionsArray = graph.addWithoutUnique(new NewArrayNode(elementType, alForStarPositions, true));
              alForStarPositions.setNext(startPositionsArray);

              ConstantNode constant0 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(0), StampFactory.forInteger(32)));
              ConstantNode constant1 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(1), StampFactory.forInteger(32)));
              ConstantNode constantMinus1 = graph.addOrUnique(new ConstantNode(JavaConstant.forInt(-1), StampFactory.forInteger(32)));

              LoadIndexedNode liShip0 = graph.add(new LoadIndexedNode(null, toBeCompressedArray, constant0, null, JavaKind.Int));
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

              /*15*/
              EndNode endBeforeCompressionLoop = graph.addWithoutUnique(new EndNode());
              storeLengthsFirstVal.setNext(endBeforeCompressionLoop);
              storeLengthsFirstVal.setStateAfter(st);

              LoopBeginNode beginCompressionLoop = graph.add(new LoopBeginNode());
              beginCompressionLoop.addForwardEnd(endBeforeCompressionLoop);
              beginCompressionLoop.setStateAfter(st);


              //loop duration
              ArrayLengthNode alForIteration = graph.add(new ArrayLengthNode(toBeCompressedArray));
              beginCompressionLoop.setNext(alForIteration);

              //iteration variable
              /*18*/
              ValuePhiNode iterationVar = graph.addWithoutUnique(
                  new ValuePhiNode(StampFactory.forInteger(32), beginCompressionLoop)
              );

              /*48*/
              AddNode inputVarIncrement = graph.addWithoutUnique(new AddNode(iterationVar, constant1));

              iterationVar.addInput(constant1);
              iterationVar.addInput(inputVarIncrement);

              /*31*/
              AddNode indexMinusForArrayComparison = graph.addWithoutUnique(new AddNode(iterationVar, constantMinus1));
              IntegerLessThanNode lessThanArrayLength = graph.addWithoutUnique(new IntegerLessThanNode(iterationVar, alForIteration));

              /*27*/
              BeginNode startOfComparison = graph.add(new BeginNode());
              LoopExitNode exitComparison = graph.add(new LoopExitNode(beginCompressionLoop));
              exitComparison.setStateAfter(st);

              IfNode loopCondition = graph.add(new IfNode(lessThanArrayLength, startOfComparison, exitComparison, 0.9));

              alForIteration.setNext(loopCondition);

              //continue with the inner loop process
              /*29*/
              LoadIndexedNode loadCurrentValue = graph.add(new LoadIndexedNode(null, toBeCompressedArray, iterationVar, null, JavaKind.Int));
              startOfComparison.setNext(loadCurrentValue);

              LoadIndexedNode loadPreviousValue = graph.add(new LoadIndexedNode(null, toBeCompressedArray, indexMinusForArrayComparison, null, JavaKind.Int));
              loadCurrentValue.setNext(loadPreviousValue);

              //load values for comparison
              IntegerEqualsNode checkConsecutiveValues = graph.addOrUnique(new IntegerEqualsNode(loadCurrentValue, loadPreviousValue));
              /*34*/
              BeginNode ccvFalseSuccessor = graph.add(new BeginNode());
              BeginNode ccvTrueSuccessor = graph.add(new BeginNode());

              //check if two consecutive values are different
              IfNode consecutiveValuesComparison = graph.add(new IfNode(checkConsecutiveValues, ccvTrueSuccessor, ccvFalseSuccessor, 0.7));

              loadPreviousValue.setNext(consecutiveValuesComparison);

              /*43*/
              EndNode endCcvTrueSuccessor = graph.addWithoutUnique(new EndNode());
              ccvTrueSuccessor.setNext(endCcvTrueSuccessor);

              /*37*/
              LoadIndexedNode readNewStoringValue = graph.add(new LoadIndexedNode(null, toBeCompressedArray, iterationVar, null, JavaKind.Int));
              ccvFalseSuccessor.setNext(readNewStoringValue);

              /*17*/
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

              /*42*/
              AddNode compIndexIncrement = graph.addWithoutUnique(new AddNode(compArrayIndex, constant1));

              /*46*/
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

              /*24*/
              ValueProxyNode sendCompressedLength = graph.addOrUnique(new ValueProxyNode(compArrayIndex, exitComparison));

              //exit to array operation
              /*50*/
              ArrayLengthNode alForLastStartPos = graph.add(new ArrayLengthNode(toBeCompressedArray));
              exitComparison.setNext(alForLastStartPos);

              /*51*/
              StoreIndexedNode storeLastPosition = graph.add(new StoreIndexedNode(startPositionsArray,
                  sendCompressedLength,
                  null,
                  null,
                  JavaKind.Int,
                  alForLastStartPos));
              alForLastStartPos.setNext(storeLastPosition);
              storeLastPosition.setStateAfter(st);

              storeLastPosition.setNext(endBeforeLoop);

              // The arrayLength from the pattern is fetched in the beginning
              /*61*/
              IntegerLessThanNode changeTheArrayIterationComparison = null;
              for(Node n :alOfShip.usages().snapshot()){
                if (n instanceof IntegerLessThanNode ){
                  changeTheArrayIterationComparison = (IntegerLessThanNode) n;
                }
              }

              /*53*/
              AddNode decreaseProxyForComp = graph.addWithoutUnique(new AddNode(sendCompressedLength, constantMinus1));

              /*59*/
              ValuePhiNode iteratorInOperationLoop = (ValuePhiNode) changeTheArrayIterationComparison.getX();

              IntegerLessThanNode newOperationLoopComparison =
                  graph.addOrUnique(new IntegerLessThanNode(decreaseProxyForComp, iteratorInOperationLoop));

              changeTheArrayIterationComparison.replaceAtUsagesAndDelete(newOperationLoopComparison);

              IfNode comparisonToEnterOpLoop = (IfNode) alOfShip.next();

              LoopBeginNode operationLoopBegNode = (LoopBeginNode) bindNodes.get(0);

              alOfShip.setNext(null);
              operationLoopBegNode.setNext(comparisonToEnterOpLoop);
              alOfShip.safeDelete();

              Node falseTemp = comparisonToEnterOpLoop.falseSuccessor();
              Node trueTemp =  comparisonToEnterOpLoop.trueSuccessor();
              comparisonToEnterOpLoop.setFalseSuccessor(null);
              comparisonToEnterOpLoop.setTrueSuccessor(null);
              comparisonToEnterOpLoop.setFalseSuccessor((AbstractBeginNode) trueTemp);
              comparisonToEnterOpLoop.setTrueSuccessor((AbstractBeginNode) falseTemp);
              comparisonToEnterOpLoop.setTrueSuccessorProbability(1 - comparisonToEnterOpLoop.getTrueSuccessorProbability());

              /*69*/
              LoadIndexedNode loadForPredicate = (LoadIndexedNode)  bindNodes.get(2);
              loadForPredicate.setArray(runsArray);

              LoadIndexedNode loadForSecondPredicate = (LoadIndexedNode)  bindNodes.get(3);
              loadForSecondPredicate.setArray(runsArray);

              /*76*/
              // TODO: Check that it is the node you get below in bindNodes list
              LoadIndexedNode loadArrayForSum = (LoadIndexedNode)  bindNodes.get(4);
              loadArrayForSum.setArray(runsArray);

              /*86*/
              EndNode endOfSumOperation = (EndNode) loadArrayForSum.next();

              /*82*/
              SignExtendNode extendSum = null;
              for (Node loadUsages: loadArrayForSum.usages().snapshot()){
                if (loadUsages instanceof  SignExtendNode) {
                  extendSum = (SignExtendNode) loadUsages;
                }
              }

              //Grab the add node of iterator in loop
              AddNode iteratorIncrease = null;
              for(Node iteratorUsage: iteratorInOperationLoop.usages().snapshot()){
                if (iteratorUsage instanceof AddNode){
                  iteratorIncrease = (AddNode) iteratorUsage;
                }
              }

              /*78*/
              LoadIndexedNode loadNextStartPosition =  graph.add(new LoadIndexedNode(null, startPositionsArray, iteratorIncrease, null, JavaKind.Int));
              loadArrayForSum.setNext(loadNextStartPosition);

              LoadIndexedNode loadCurrentStartPos =  graph.add(new LoadIndexedNode(null, startPositionsArray, iteratorInOperationLoop, null, JavaKind.Int));
              loadNextStartPosition.setNext(loadCurrentStartPos);
              loadCurrentStartPos.setNext(endOfSumOperation);

              /*80*/
              SubNode findLengthFromStartPositions = graph.addWithoutUnique(new SubNode(loadNextStartPosition, loadCurrentStartPos));

              MulNode runTimesLength = graph.addOrUnique(new MulNode(loadArrayForSum, findLengthFromStartPositions));
              extendSum.setValue(runTimesLength);

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
          for (PatternNode[] ptn : getNewPattern(pattern, next)) {
            matchSecond(next, ptn);
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