/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Depth.Expr
public import QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Execution.Circuit
import all QuantumAlg.Core.Base.Depth.Expr
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

/-- The built-in Z measurement coordinate is fixed by the measured wire's dimension. -/
def zEvent (dimension : ℕ+) : Resource.Event .quantum :=
  .measurement { family := "builtin", name := "z", parameters := [dimension] }

/-- Ordered native operations on the path returned by the circuit interpreter. -/
public def eventTrace {kind : ProblemKind} {pre post : RuntimeCtx kind} :
    (code : Circuit pre post) → code.Path → List (Resource.Event kind)
  | .id _, _ => []
  | .classical op, _ => op.eventTrace
  | .declaredCall call, _ => [call.event]
  | .unitary program _, _ => program.eventTrace
  | .measureZ (ctx := ctx) wire _, _ => [zEvent (ctx.quantumLayout.wire wire).dimension]
  | .randomBits width _, _ => [.classicalOperation (.randomBits width)]
  | .retain _ _ _ _, _ => []
  | .prepare _ _ _ _ _ preparation, _ => [preparation.event]
  | .seq first second, path => first.eventTrace path.1 ++ second.eventTrace path.2
  | .branch _ body, path => (body path.1).eventTrace path.2
  | .iterate count body, path =>
      (List.ofFn (fun index : Fin count => body.eventTrace (path index))).flatten
  | .workspace _ _ _ _ body, path => body.eventTrace path

/-- Exact native event multiplicities, obtained by forgetting only the trace's order. -/
public def resourcePool {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) : ResourcePool kind :=
  ResourcePool.ofList (code.eventTrace path)

/-- The exact contexts visited by the selected instruction bodies. -/
public def visitedContexts {kind : ProblemKind} {pre post : RuntimeCtx kind} :
    (code : Circuit pre post) → code.Path → List (RuntimeCtx kind)
  | .id ctx, _ => [ctx]
  | .classical (ctx := ctx) _, _ => [ctx]
  | .declaredCall (ctx := ctx) _, _ => [ctx]
  | .unitary (ctx := ctx) _ _, _ => [ctx]
  | .measureZ (ctx := ctx) _ _, _ => [ctx]
  | .randomBits (ctx := ctx) _ _, _ => [ctx]
  | .retain ctx key shape fresh, _ => [ctx, ctx.addRetained key shape fresh]
  | .prepare ctx key layout fresh disjoint _, _ =>
      [ctx, ctx.addOwnedLayout key layout fresh disjoint]
  | .seq first second, path =>
      first.visitedContexts path.1 ++ second.visitedContexts path.2
  | .branch _ body, path => (body path.1).visitedContexts path.2
  | .iterate (ctx := ctx) count body, path =>
      ctx :: (List.ofFn (fun index : Fin count => body.visitedContexts (path index))).flatten
  | .workspace ctx _ _ _ body, path => ctx :: body.visitedContexts path ++ [ctx]

private def peak {kind : ProblemKind} (projection : RuntimeCtx kind → SpacePool kind)
    (contexts : List (RuntimeCtx kind)) : SpacePool kind :=
  contexts.foldr (fun ctx current => SpacePool.max (projection ctx) current) 0

/-- Resident peak includes every live system and classical cell on the actual path. -/
public def peakResidentSpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) : SpacePool kind :=
  peak RuntimeCtx.residentSpace (code.visitedContexts path)

/-- Auxiliary peak follows the roles of those same actual live entries. -/
public def peakAuxiliarySpace {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (path : code.Path) : SpacePool kind :=
  peak RuntimeCtx.auxiliarySpace (code.visitedContexts path)

/-- Native event dependencies of the same executed path, including classical feed-forward. -/
public def eventDepth {kind : ProblemKind} {pre post : RuntimeCtx kind} :
    (code : Circuit pre post) → code.Path → DepthExpr (Resource.Event kind)
  | .id _, _ => .id
  | .classical op, _ => .atom op.event
  | .declaredCall call, _ => .atom call.event
  | .unitary program _, _ => program.eventDepth
  | .measureZ (ctx := ctx) wire _, _ => .atom (zEvent (ctx.quantumLayout.wire wire).dimension)
  | .randomBits width _, _ => .atom (.classicalOperation (.randomBits width))
  | .retain _ _ _ _, _ => .id
  | .prepare _ _ _ _ _ preparation, _ => .atom preparation.event
  | .seq first second, path => .seq (first.eventDepth path.1) (second.eventDepth path.2)
  | .branch _ body, path => (body path.1).eventDepth path.2
  | .iterate count body, path =>
      .indexedProduct "circuit-iteration" count .id (fun index => body.eventDepth (path index))
  | .workspace _ _ _ _ body, path => body.eventDepth path

/-- Evaluate path depth under the independent specification's native event durations. -/
public def depth {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (duration : Resource.Event kind → Nat) (path : code.Path) : Nat :=
  DepthExpr.depthEval duration (code.eventDepth path)

/-- Conditional execution charges precisely the body indexed by its recorded read. -/
theorem eventTrace_branch {kind : ProblemKind} {pre post : RuntimeCtx kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit pre post)
    (value : shape.Value) (path : (body value).Path) :
    (Circuit.branch input body).eventTrace ⟨value, path⟩ = (body value).eventTrace path := rfl

/-- Sequential depth retains the dependence between successive executed bodies. -/
theorem depth_seq {kind : ProblemKind} {pre mid post : RuntimeCtx kind}
    (first : Circuit pre mid) (second : Circuit mid post)
    (duration : Resource.Event kind → Nat) (left : first.Path) (right : second.Path) :
    (Circuit.seq first second).depth duration (left, right) =
      first.depth duration left + second.depth duration right := rfl

end QuantumAlg.Circuit
