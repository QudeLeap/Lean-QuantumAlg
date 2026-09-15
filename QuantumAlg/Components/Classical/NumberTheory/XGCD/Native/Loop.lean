/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Guarded
import all QuantumAlg.Core.Execution.Classical.Iteration

/-!
# Actual stored-condition extended-Euclidean iteration

The existing iterate instruction composes the actual selected store record.
Each finite path entry is obtained from the store at that iteration, retaining
the complete quantum-reference state and all unchanged caller readings.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual final store and the real branch path at every finite iteration stage. -/
def iteratedActiveRecord (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (guardedActive cells zero).Path)
    (count : Nat) (store : Store ctx) : Store ctx ×
      (Circuit.iterate count (guardedActive cells zero)).Path :=
  ((fun before => (record before).1)^[count] store,
    fun index => (record ((fun before => (record before).1)^[index.val] store)).2)

/-- The same actual record interprets every full input density and finite history. -/
theorem xgcdNativeLoop_execute (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (guardedActive cells zero).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (guardedActive cells zero).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2))))
    (count : Nat) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (Circuit.iterate count (guardedActive cells zero)).execute Reference state =
      state.mapClassical (fun entry =>
        ((iteratedActiveRecord cells zero record count entry.1).1,
          (entry.2, (iteratedActiveRecord cells zero record count entry.1).2))) := by
  refine (Circuit.execute_iterate_mapClassical
    (guardedActive cells zero) record equation count Reference state).trans ?_
  let update : Store ctx × History → Store ctx ×
      (History × (Circuit.iterate count (guardedActive cells zero)).Path) :=
    fun entry => ((iteratedActiveRecord cells zero record count entry.1).1,
      (entry.2, (iteratedActiveRecord cells zero record count entry.1).2))
  exact congrArg
    (fun decision : DecidableEq (Store ctx ×
        (History × (Circuit.iterate count (guardedActive cells zero)).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference)
        decision state update)
    (Subsingleton.elim _ _)

/-- A caller read preserved by each actual selected record survives every iteration count. -/
theorem xgcdNativeLoop_read_other (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (guardedActive cells zero).Path)
    {shape : CShape} (other : CInputRef ctx shape)
    (preserved : ∀ before : Store ctx, ((record before).1).read other = before.read other)
    (count : Nat) (store : Store ctx) :
    ((iteratedActiveRecord cells zero record count store).1).read other = store.read other := by
  change (((fun before => (record before).1)^[count]) store).read other = _
  induction count generalizing store with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact (inductionHypothesis (record store).1).trans (preserved store)

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
