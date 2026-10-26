/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Core.Base.Depth.Transform
public import QuantumAlg.Core.Base.Accounting.Event.Composition
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Actual circuit path accounting

Events, visited live contexts, and critical-path expressions are interpreted
from the same instruction syntax and finite path recorded during execution.
A classical branch contributes only its selected body's operations. Sequential
composition preserves the dependency from measurement to classical processing
and subsequent conditional gates.

Space is derived from actual visited contexts at each native dimension. External
proof references and mathematical path records do not allocate runtime entries.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

/-- The built-in Z measurement coordinate is fixed by the measured wire's dimension. -/
@[expose] public def zEvent {gates : GateModel} {oracles : OracleModel}
    (dimension : ℕ+)
    (operations : ClassicalOpModel := .empty)
    (classicalOracles : ClassicalOracleModel := .empty) :
    Resource.Event (.quantum gates oracles operations classicalOracles) := .measurement dimension

/-- Ordered native operations on the path returned by the circuit interpreter. -/
@[expose] public def eventTrace {allowAllocation : Bool}
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} :
    (code : Circuit model pre post allowAllocation) → code.Path → List (Resource.Event model)
  | .id _, _ => []
  | .classical (model := model) application, _ =>
      [.classicalOperation (model.classicalOperations.coordinate application.token)]
  | .classicalQuery (model := model) application, _ =>
      [.classicalQuery (model.classicalOracles.coordinate application.query)]
  | .unitary (operations := operations) (classicalOracles := classicalOracles) program, _ =>
      program.eventTrace operations classicalOracles
  | .measureZ (ctx := ctx) (operations := operations)
      (classicalOracles := classicalOracles) wire _, _ =>
      [zEvent (ctx.quantumLayout.wire wire).dimension operations classicalOracles]
  | .retain _ _ _ _, _ => []
  | .prepareZero (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := classicalOracles) _ _ layout _ _, _ =>
      ZeroPreparation.eventTrace gates oracles layout operations classicalOracles
  | .seq first second, path => first.eventTrace path.1 ++ second.eventTrace path.2
  | .branch _ body, path => (body path.1).eventTrace path.2
  | .iterate count body, path =>
      (List.ofFn (fun index : Fin count => body.eventTrace (path index))).flatten
  | .workspace _ _ _ _ body, path => body.eventTrace path
  | .embed _ body, path => body.eventTrace path
  | .ownedLayoutView _ body, path => body.eventTrace path
  | .parallelClassical (operations := operations) join _ first second, path =>
      (first.eventTrace path.1).map (Resource.Event.serviceClassicalLeft join operations) ++
        (second.eventTrace path.2).map (Resource.Event.serviceClassicalRight join operations)
  | .parallelQuantum (gates := gates) (oracles := oracles) (operations := operations)
      join _ first second, path =>
      (first.eventTrace path.1).map (Resource.Event.serviceQuantumLeft join gates oracles
          operations) ++
        (second.eventTrace path.2).map
          (Resource.Event.serviceQuantumRight join gates oracles operations)

/-- Exact native event multiplicities, obtained by forgetting only the trace's order. -/
public def resourcePool {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) : ResourcePool model :=
  ResourcePool.ofList (code.eventTrace path)

/-- One native event coordinate is counted on the actual paths of both sequential components. -/
public lemma resourcePool_count_seq {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid allowAllocation) (second : Circuit model mid post
        allowAllocation)
    (event : Resource.Event model) (path : (first.seq second).Path) :
    ResourcePool.count event ((first.seq second).resourcePool path) =
      ResourcePool.count event (first.resourcePool path.1) +
      ResourcePool.count event (second.resourcePool path.2) := by
  change ResourcePool.count event
    (first.resourcePool path.1 + second.resourcePool path.2) = _
  exact ResourcePool.count_add _ _ _

/-- The exact contexts visited by the selected instruction bodies. -/
public def visitedContexts {allowAllocation : Bool}
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} :
    (code : Circuit model pre post allowAllocation) → code.Path → List (RuntimeCtx model.kind)
  | .id ctx, _ => [ctx]
  | .classical (ctx := ctx) _, _ => [ctx]
  | .classicalQuery (ctx := ctx) _, _ => [ctx]
  | .unitary (ctx := ctx) _, _ => [ctx]
  | .measureZ (ctx := ctx) _ _, _ => [ctx]
  | .retain ctx key shape fresh, _ => [ctx, ctx.addRetained key shape fresh]
  | .prepareZero ctx key layout fresh disjoint, _ =>
      [ctx, ctx.addOwnedLayout key layout fresh disjoint]
  | .seq first second, path =>
      first.visitedContexts path.1 ++ second.visitedContexts path.2
  | .branch _ body, path => (body path.1).visitedContexts path.2
  | .iterate (ctx := ctx) count body, path =>
      ctx :: (List.ofFn (fun index : Fin count => body.visitedContexts (path index))).flatten
  | .workspace ctx _ _ _ body, path => ctx :: body.visitedContexts path ++ [ctx]
  | .embed (caller := caller) _ _, _ => [caller]
  | .ownedLayoutView (original := original) _ _, _ => [original]
  | .parallelClassical (left := left) (right := right) _ separate _ _, _ =>
      [left.disjointUnion right separate]
  | .parallelQuantum (left := left) (right := right) _ separate _ _, _ =>
      [left.disjointUnion right separate]

private def peak {kind : ProblemKind} (projection : RuntimeCtx kind → SpacePool kind)
    (contexts : List (RuntimeCtx kind)) : SpacePool kind :=
  contexts.foldr (fun ctx current => SpacePool.max (projection ctx) current) 0

/-- Resident peak includes every live system and classical cell on the actual path. -/
public def peakResidentSpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) : SpacePool model.kind :=
  peak RuntimeCtx.residentSpace (code.visitedContexts path)

/-- Auxiliary peak follows the roles of those same actual live entries. -/
public def peakAuxiliarySpace {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) : SpacePool model.kind :=
  peak RuntimeCtx.auxiliarySpace (code.visitedContexts path)

/-- Native event dependencies of the same executed path, including classical feed-forward. -/
public def eventDepth {allowAllocation : Bool}
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} :
    (code : Circuit model pre post allowAllocation) → code.Path → DepthExpr (Resource.Event model)
  | .id _, _ => .id
  | .classical (model := model) application, _ =>
      .atom (.classicalOperation (model.classicalOperations.coordinate application.token))
  | .classicalQuery (model := model) application, _ =>
      .atom (.classicalQuery (model.classicalOracles.coordinate application.query))
  | .unitary (operations := operations) (classicalOracles := classicalOracles) program, _ =>
      program.eventDepth operations classicalOracles
  | .measureZ (ctx := ctx) (operations := operations)
      (classicalOracles := classicalOracles) wire _, _ =>
      .atom (zEvent (ctx.quantumLayout.wire wire).dimension operations classicalOracles)
  | .retain _ _ _ _, _ => .id
  | .prepareZero (gates := gates) (oracles := oracles) (operations := operations)
      (classicalOracles := classicalOracles) _ _ layout _ _, _ =>
      ZeroPreparation.eventDepth gates oracles layout operations classicalOracles
  | .seq first second, path => .seq (first.eventDepth path.1) (second.eventDepth path.2)
  | .branch _ body, path => (body path.1).eventDepth path.2
  | .iterate count body, path =>
      .indexedProduct "circuit-iteration" count .id (fun index => body.eventDepth (path index))
  | .workspace _ _ _ _ body, path => body.eventDepth path
  | .embed _ body, path => body.eventDepth path
  | .ownedLayoutView _ body, path => body.eventDepth path
  | .parallelClassical (operations := operations) join _ first second, path =>
      .tensor
        (DepthExpr.mapSchedule false (Resource.Event.serviceClassicalLeft join operations)
          (first.eventDepth path.1))
        (DepthExpr.mapSchedule false (Resource.Event.serviceClassicalRight join operations)
          (second.eventDepth path.2))
  | .parallelQuantum (gates := gates) (oracles := oracles) (operations := operations)
      join _ first second, path =>
      .tensor
        (DepthExpr.mapSchedule false
          (Resource.Event.serviceQuantumLeft join gates oracles operations) (first.eventDepth
              path.1))
        (DepthExpr.mapSchedule false
          (Resource.Event.serviceQuantumRight join gates oracles operations) (second.eventDepth
              path.2))

/-- Evaluate path depth under the independent specification's native event durations. -/
public def depth {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (duration : Resource.Event model → Nat)
    (path : code.Path) : Nat :=
  DepthExpr.depthEval duration (code.eventDepth path)

/-- Conditional execution charges precisely the body indexed by its recorded read. -/
lemma eventTrace_branch {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit model pre post allowAllocation)
    (value : shape.Value) (path : (body value).Path) :
    (Circuit.branch input body).eventTrace ⟨value, path⟩ = (body value).eventTrace path := rfl

/-- Sequential depth retains the dependence between successive executed bodies. -/
lemma depth_seq {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
    (first : Circuit model pre mid allowAllocation) (second : Circuit model mid post
        allowAllocation)
    (duration : Resource.Event model → Nat) (left : first.Path) (right : second.Path) :
    (Circuit.seq first second).depth duration (left, right) =
      first.depth duration left + second.depth duration right := rfl

end QuantumAlg.Circuit
