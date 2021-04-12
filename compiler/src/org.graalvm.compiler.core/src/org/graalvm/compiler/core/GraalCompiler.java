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

import org.graalvm.compiler.code.CompilationResult;
import org.graalvm.compiler.core.common.PermanentBailoutException;
import org.graalvm.compiler.core.common.RetryableBailoutException;
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
import org.graalvm.compiler.nodes.BeginNode;
import org.graalvm.compiler.nodes.EndNode;
import org.graalvm.compiler.nodes.FixedGuardNode;
import org.graalvm.compiler.nodes.FixedNode;
import org.graalvm.compiler.nodes.FixedWithNextNode;
import org.graalvm.compiler.nodes.IfNode;
import org.graalvm.compiler.nodes.Invoke;
import org.graalvm.compiler.nodes.InvokeNode;
import org.graalvm.compiler.nodes.LoopBeginNode;
import org.graalvm.compiler.nodes.LoopEndNode;
import org.graalvm.compiler.nodes.StructuredGraph;
import org.graalvm.compiler.nodes.graphbuilderconf.GraphBuilderConfiguration;
import org.graalvm.compiler.nodes.graphbuilderconf.IntrinsicContext;
import org.graalvm.compiler.nodes.java.ArrayLengthNode;
import org.graalvm.compiler.nodes.java.LoadIndexedNode;
import org.graalvm.compiler.nodes.java.NewArrayNode;
import org.graalvm.compiler.phases.OptimisticOptimizations;
import org.graalvm.compiler.phases.PhaseSuite;
import org.graalvm.compiler.phases.common.DeadCodeEliminationPhase;
import org.graalvm.compiler.phases.common.inlining.InliningUtil;
import org.graalvm.compiler.phases.tiers.HighTierContext;
import org.graalvm.compiler.phases.tiers.LowTierContext;
import org.graalvm.compiler.phases.tiers.MidTierContext;
import org.graalvm.compiler.phases.tiers.Suites;
import org.graalvm.compiler.phases.tiers.TargetProvider;
import org.graalvm.compiler.phases.util.Providers;

import jdk.vm.ci.meta.ProfilingInfo;
import jdk.vm.ci.meta.ResolvedJavaMethod;

import java.util.ArrayList;

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
  private static ArrayList<PatternNode[]> plist = new ArrayList<>();
  private static ArrayList<Node> nlist = new ArrayList<>();
  private static ArrayList<Node> checkedNodes = new ArrayList<>();

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
            /*new PatternNode(new NewArrayNode(), (x) -> {
              Node child = ((FixedWithNextNode) x).next();
              BeginNode b = graph.add(new BeginNode());
              graph.addAfterFixed((FixedWithNextNode) x, b);
              ((FixedWithNextNode) x).setNext(b);
              graph.addAfterFixed(b, (FixedWithNextNode) child);
            }), new AncestorNode(),*/ new PatternNode(new LoopBeginNode(), (x) -> {
              Node child = ((FixedWithNextNode) x).next();
              BeginNode b = graph.add(new BeginNode());
              graph.addAfterFixed((FixedWithNextNode) x, b);
              ((FixedWithNextNode) x).setNext(b);
              graph.addAfterFixed(b, (FixedWithNextNode) child);
            }), /*new PatternNode(new ArrayLengthNode()),*/
            new AncestorNode(),
            new PatternNode(new IfNode()), new IndexNode(0), new PatternNode(new BeginNode()),
            new PatternNode(new LoadIndexedNode()),/* new PatternNode(new FixedGuardNode()),*/
            new AncestorNode(), new PatternNode(new LoadIndexedNode()), /*new PatternNode(new LoadIndexedNode()),*/
            new PatternNode(new EndNode()));
      }

      suites.getHighTier().apply(graph, highTierContext);
      graph.maybeCompress();
      debug.dump(DebugContext.BASIC_LEVEL, graph, "After high tier");

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

    PatternNode() {
    }

    PatternNode(Node node) {
      this.currentNode = node;
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

    @Override
    public boolean equals(Object o) {
      return true;
    }
  }

  public static class AncestorNode extends PatternNode {
    public Node currentNode = null;

    @Override
    public boolean equals(Object o) {
      return true;
    }
  }

  public static PatternNode[] getNewPattern(PatternNode[] currentPattern, Node nextNode) {
    if (!(currentPattern[0] instanceof AncestorNode)) {
      int newPatternLength = currentPattern.length - 1;
      PatternNode[] newPattern = new PatternNode[newPatternLength];
      System.arraycopy(currentPattern, 1, newPattern, 0, newPatternLength);
      return newPattern;
    } else if (currentPattern[1].equals(nextNode.getClass())) {
      nlist.add(nextNode);
      plist.add(currentPattern);
      int newPatternLength = currentPattern.length - 1;
      PatternNode[] newPattern = new PatternNode[newPatternLength];
      System.arraycopy(currentPattern, 1, newPattern, 0, newPatternLength);
      return newPattern;
    } else {
      return currentPattern;
    }
  }

  public static ArrayList<Node> getNext(Node currentNode) {
    ArrayList<Node> result = new ArrayList<Node>();

    if (currentNode instanceof FixedWithNextNode) {
      result.add(((FixedWithNextNode) currentNode).next());
    } else if (currentNode instanceof IfNode) {
      result.add(((IfNode) currentNode).trueSuccessor());
      result.add(((IfNode) currentNode).falseSuccessor());
    } /*else if (currentNode instanceof EndNode) {
      for(Node node:currentNode.usages() ) {
        result.add(node);
      }
    }*/
    return result;
  }

  private static boolean firstTime = true;

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
      if (nlist.size() > 0) {
        int lastIndex = nlist.size() - 1;
        if(checkedNodes.contains(nlist.get(lastIndex))){
          plist.remove(lastIndex);
          nlist.remove(lastIndex);
        }
        if (nlist.size() > 0) {
          lastIndex = nlist.size() - 1;
          matchSecond(nlist.get(lastIndex), plist.get(lastIndex));
        }
      } else {
        System.out.println("no match");
        return;
      }
    } else {
      if (pattern.length > 1) {
        if (pattern.length > 2 && pattern[1] instanceof IndexNode) {
          Node next = getNext(incomingMatch).get(((IndexNode) pattern[1]).index);
          matchSecond(next, getNewPattern(getNewPattern(pattern, next), next));
        }

        for (Node next : getNext(incomingMatch)) {
          matchSecond(next, getNewPattern(pattern, next));
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