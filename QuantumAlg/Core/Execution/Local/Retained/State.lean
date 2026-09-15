/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Context.Permutation.Local.State
import all QuantumAlg.Core.Execution.Local.Framing.State
import all QuantumAlg.Core.Execution.State.Coordinate.Measurement

/-!
# Complete local execution beside arbitrary retained data

The actual existing retained head is separated only in mathematical Store and
basis coordinates. Its value, history and every quantum-reference correlation
are preserved through the original interpreter. No initial-value, preparation
or support hypothesis is needed [dW19, qcnotes.tex:5381,5405,5409].
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}
  (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)

private def retainedUnionState {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    State (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)) Reference H :=
  (state.mapClassical
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm).reindex
      (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
        Reference).symm

private theorem retainedUnionState_inverse {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    ContextPermutation.state (retainedLocalPermutation ctx key shape fresh)
      (retainedUnionState key shape fresh state) = state := by
  have inverse := ExecutionState.coordinate_transport_inverse
    (S := (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)).register.prod Reference) state
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm
    (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
      Reference).symm
  simpa only [ContextPermutation.state, retainedUnionState, Equiv.symm_symm] using inverse

private theorem retainedUnionState_permuted {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.disjointUnion (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh)) Reference H) :
    retainedUnionState key shape fresh
      (ContextPermutation.state (retainedLocalPermutation ctx key shape fresh) state) = state :=
  ContextPermutation.state_inverse (retainedLocalPermutation ctx key shape fresh) state

private theorem retainedUnionState_history {Reference : Register} {H K : Type}
    [Fintype H] [Fintype K]
    (state : State (ctx.addRetained key shape fresh) Reference H) (update : H → K) :
    retainedUnionState key shape fresh (state.mapHistory update) =
      (retainedUnionState key shape fresh state).mapHistory update := by
  unfold retainedUnionState State.mapHistory
  exact ExecutionState.coordinate_transport_diagram state
    (ContextPermutation.referenceBasis (retainedLocalPermutation ctx key shape fresh)
      Reference).symm
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) H).symm
    (ContextPermutation.recordEquiv (retainedLocalPermutation ctx key shape fresh) K).symm
    (fun record => (record.1, update record.2))
    (fun record => (record.1, update record.2)) (fun _ => rfl)

/-- Split the existing retained head while keeping its actual value in the complete history. -/
def underRetainedSplitState {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    State ctx (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)
      (Store (retainedLocalFrame (kind := kind) key shape) × H) :=
  ContextUnion.splitState ctx (retainedLocalFrame (kind := kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh) (retainedUnionState key shape fresh state)

/-- The full actual state obeys the original local execution after exact retained-cell splitting. -/
theorem underRetained_execute (code : Circuit ctx ctx) (supported : code.IsLocal)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (ctx.addRetained key shape fresh) Reference H) :
    underRetainedSplitState key shape fresh
        ((underRetained code supported key shape fresh).execute Reference state) =
      (code.execute (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)
        (underRetainedSplitState key shape fresh state)).mapHistory
          (fun record => (record.1.1,
            (record.1.2, underRetainedPathEquiv code supported key shape fresh record.2))) := by
  let original := retainedUnionState key shape fresh state
  let framed := retainedFramed code supported key shape fresh
  let permutation := retainedLocalPermutation ctx key shape fresh
  let pathMap : framed.Path ≃ (underRetained code supported key shape fresh).Path :=
    ContextPermutation.localPathEquiv framed
    (retainedFramed_isLocal code supported key shape fresh)
    (ctx.addRetained key shape fresh) permutation
  have permuted :
      (underRetained code supported key shape fresh).execute Reference
          (ContextPermutation.state permutation original) =
        (ContextPermutation.state permutation (framed.execute Reference original)).mapHistory
          (fun record => (record.1, pathMap record.2)) :=
    ContextPermutation.localCircuit_execute framed
      (retainedFramed_isLocal code supported key shape fresh)
      (ctx.addRetained key shape fresh) permutation Reference original
  have restored : ContextPermutation.state permutation original = state :=
    retainedUnionState_inverse key shape fresh state
  rw [restored] at permuted
  have actual :
      retainedUnionState key shape fresh
          ((underRetained code supported key shape fresh).execute Reference state) =
        (framed.execute Reference original).mapHistory
          (fun record => (record.1, pathMap record.2)) := by
    rw [permuted, retainedUnionState_history, retainedUnionState_permuted]
  change ContextUnion.splitState ctx (retainedLocalFrame (kind := kind) key shape)
    (retainedLocalDisjoint ctx key shape fresh)
    (retainedUnionState key shape fresh
      ((underRetained code supported key shape fresh).execute Reference state)) = _
  rw [actual, ContextUnion.contextUnion_splitState_mapHistory]
  let frameMap : code.Path ≃ framed.Path :=
    ContextUnion.frameLocalPathEquiv code supported (retainedLocalFrame key shape)
      (retainedLocalDisjoint ctx key shape fresh)
  have localExecution :
      ContextUnion.splitState ctx (retainedLocalFrame (kind := kind) key shape)
          (retainedLocalDisjoint ctx key shape fresh) (framed.execute Reference original) =
        (code.execute
          (Register.prod (retainedLocalFrame (kind := kind) key shape).register Reference)
          (ContextUnion.splitState ctx (retainedLocalFrame key shape)
            (retainedLocalDisjoint ctx key shape fresh) original)).mapHistory
              (fun record => (record.1.1, (record.1.2, frameMap record.2))) :=
    ContextUnion.frameLocal_execute code supported
      (retainedLocalFrame (kind := kind) key shape)
      (retainedLocalDisjoint ctx key shape fresh) Reference original
  rw [localExecution, State.mapHistory_comp]
  rfl

end

end QuantumAlg.Circuit
