/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Construction
import all QuantumAlg.Core.Execution.Classical.Composition.Unitary
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Feedback.Identity

/-!
# Actual stored feedback and its complete deterministic native record

Every real branch reads its original retained exponent cell. The complete
native operator product and chronological path are derived from the actual
prefix interpreter, with every old Store/history/reference block retained
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The selected one-bit feedback retains the actual value read by its branch. -/
def feedbackBitPath (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (store : Store (Context base noQuantum m ell width)) :
    (feedbackBit base noQuantum m ell width inverse separation previous).Path := by
  change (value : CShape.Value (.finite 2)) × Unit
  exact ⟨store.read (.storage previous.toCStorageRef), ()⟩

/-- Each path contains precisely the values read from the original retained output cells. -/
def feedbackPath (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → (bounded : count ≤ position.val) →
      Store (Context base noQuantum m ell width) →
        (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).Path
  | 0, _, _ => ()
  | count + 1, bounded, store =>
      (feedbackPath inverse outputs position count (by omega) store,
        feedbackBitPath base noQuantum m ell width inverse (position.val - count - 1)
          (outputs ⟨count, by have bound := position.isLt; omega⟩) store)

/-- Product of exactly the native phase operators selected by the same actual Store. -/
def feedbackAction (environment : OracleModel.empty.Interpretation) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Store (Context base noQuantum m ell width) →
        UnitaryOperator (Context base noQuantum m ell width).register
  | 0, _, _ => 1
  | count + 1, bounded, store =>
      ((feedbackProgram base noQuantum m ell width inverse (position.val - count - 1)
        (store.read (.storage
          (outputs ⟨count, by have bound := position.isLt; omega⟩).toCStorageRef))).matrix
            environment) *
        feedbackAction environment inverse outputs position count (by omega) store

/-- The actual feedback branch executes exactly its selected native unitary and real path. -/
lemma feedbackBit_execute (inverse : Bool) (separation : Nat)
    (previous : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (feedbackBit base noQuantum m ell width inverse separation previous).execute environment
      Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((feedbackProgram base noQuantum m ell width inverse separation
          (entry.1.read (.storage previous.toCStorageRef))).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
        (fun entry => (entry.1, (entry.2.1, (entry.2.2,
          feedbackBitPath base noQuantum m ell width inverse separation previous entry.1)))) := by
  exact Circuit.selectedUnitary_execute (.storage previous.toCStorageRef)
    (feedbackProgram base noQuantum m ell width inverse separation) environment state

/-- The complete actual feedback prefix preserves the Store and all coherent reference blocks. -/
lemma feedbackPrefix_execute (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History)) :
    (feedbackPrefix base noQuantum m ell width inverse outputs position count bounded).execute
      environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position
          count bounded entry.1) (1 : UnitaryOperator Reference)).mapClassical
        (fun entry => (entry.1, (entry.2.1, (entry.2.2,
          feedbackPath base noQuantum m ell width inverse outputs position count bounded
            entry.1)))) := by
  induction count generalizing Reference History with
  | zero =>
      simp only [feedbackPrefix, feedbackAction, feedbackPath, Recycling.tensor_one,
        Recycling.applyUnitary_one]
      exact (Circuit.execute_id environment state).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  | succ count induction =>
      let previous := outputs ⟨count, by have bound := position.isLt; omega⟩
      have composed := Circuit.execute_sequenceStoreUnitaryRecord
        (feedbackPrefix base noQuantum m ell width inverse outputs position count (by omega))
        (feedbackBit base noQuantum m ell width inverse (position.val - count - 1) previous)
        (fun store => (store,
          feedbackPath base noQuantum m ell width inverse outputs position count (by omega) store))
        (fun store => (store, feedbackBitPath base noQuantum m ell width inverse
          (position.val - count - 1) previous store))
        (feedbackAction base noQuantum m ell width environment.quantum inverse outputs position
          count (by omega))
        (fun store => (feedbackProgram base noQuantum m ell width inverse
          (position.val - count - 1) (store.read (.storage previous.toCStorageRef))).matrix
            environment.quantum) environment
        (fun reference _ _ original => induction (by omega) reference original)
        (fun reference _ _ original =>
          feedbackBit_execute base noQuantum m ell width inverse (position.val - count - 1)
            previous environment reference original)
        Reference state
      exact composed

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
