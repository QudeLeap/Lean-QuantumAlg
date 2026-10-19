/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent space bounds on actual executed paths

A space budget bounds an execution when it bounds every live context visited
on that path. Sequential composition takes the coordinatewise maximum of the
two actual peaks. The statements retain the native dimension-indexed axes and
apply equally to quantum and classical circuits, including empty sequences.
-/

namespace QuantumAlg.Circuit

variable {allowAllocation : Bool}

private lemma peak_le_of_contexts {kind : ProblemKind}
    (projection : RuntimeCtx kind → SpacePool kind) (contexts : List (RuntimeCtx kind))
    (budget : SpacePool kind) (bounded : ∀ ctx ∈ contexts, projection ctx ≤ budget) :
    peak projection contexts ≤ budget := by
  induction contexts with
  | nil => exact fun axis => Nat.zero_le (budget axis)
  | cons head tail ih =>
      exact SpacePool.max_le (bounded head (.head tail))
        (ih (fun ctx member => bounded ctx (.tail head member)))

/-- A resident budget bounds the peak if it bounds every actually visited live context. -/
lemma peakResidentSpace_le_of_visited {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) (budget : SpacePool
        model.kind)
    (bounded : ∀ ctx ∈ code.visitedContexts path, ctx.residentSpace ≤ budget) :
    code.peakResidentSpace path ≤ budget :=
  peak_le_of_contexts RuntimeCtx.residentSpace _ budget bounded

/-- Auxiliary roles are bounded on the same complete list of visited contexts. -/
lemma peakAuxiliarySpace_le_of_visited {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post allowAllocation) (path : code.Path) (budget : SpacePool
        model.kind)
    (bounded : ∀ ctx ∈ code.visitedContexts path, ctx.auxiliarySpace ≤ budget) :
    code.peakAuxiliarySpace path ≤ budget :=
  peak_le_of_contexts RuntimeCtx.auxiliarySpace _ budget bounded

private lemma peak_append {kind : ProblemKind}
    (projection : RuntimeCtx kind → SpacePool kind) (left right : List (RuntimeCtx kind)) :
    peak projection (left ++ right) =
      SpacePool.max (peak projection left) (peak projection right) := by
  induction left with
  | nil =>
      apply SpacePool.ext
      intro axis
      exact (Nat.zero_max _).symm
  | cons head tail ih =>
      change SpacePool.max (projection head) (peak projection (tail ++ right)) = _
      rw [ih]
      exact (SpacePool.max_assoc _ _ _).symm

/-- Sequential resident peak is exactly the maximum of the two actual execution peaks. -/
lemma peakResidentSpace_seq {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle allowAllocation) (second : Circuit model middle post
        allowAllocation)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).peakResidentSpace path =
      SpacePool.max (first.peakResidentSpace path.1) (second.peakResidentSpace path.2) :=
  peak_append RuntimeCtx.residentSpace _ _

/-- Sequential auxiliary peak is exactly the maximum for the same two path segments. -/
lemma peakAuxiliarySpace_seq {model : ExecutionModel}
    {pre middle post : RuntimeCtx model.kind}
    (first : Circuit model pre middle allowAllocation) (second : Circuit model middle post
        allowAllocation)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).peakAuxiliarySpace path =
      SpacePool.max (first.peakAuxiliarySpace path.1) (second.peakAuxiliarySpace path.2) :=
  peak_append RuntimeCtx.auxiliarySpace _ _

end QuantumAlg.Circuit
