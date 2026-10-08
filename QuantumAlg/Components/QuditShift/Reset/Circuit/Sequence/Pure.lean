/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.State
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.SelectionAll

/-!
# Pure physical output of an actual complete reset

Every complete reset record has the same predetermined local basis state after
the external reference is observed away. The proof uses the full executed
block, including its actual measurement history and zero-weight records.
-/

namespace QuantumAlg.QuditShift

noncomputable section

open Execution

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}
  (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)

/-- Every actual reset record has the prescribed pure state on all physical systems. -/
theorem resetToBasis_pure_fullSelection
    (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (label : ctx.quantumLayout.Basis) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((ExecutionModel.quantum gates oracles).HiddenState × History))
    (record : Store ctx × ((ExecutionModel.quantum gates oracles).HiddenState ×
      (History × (resetToBasis implementations outputs label).Path))) :
    (StatePromise.pure (NormalizedVector.ket
      (R := ctx.quantumLayout.selectedRegister Finset.univ)
      (ctx.quantumLayout.restrictSelectedBasis Finset.univ label))).Holds
        (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
          (((resetToBasis implementations outputs label).execute
            Reference state).block record)) := by
  let joint := ((resetToBasis implementations outputs label).execute Reference state).block record
  let selection : ctx.register.Index ≃
      (ctx.quantumLayout.selectedRegister Finset.univ).Index := by
    change ctx.quantumLayout.Basis ≃ ctx.quantumLayout.SelectedBasis Finset.univ
    exact ctx.quantumLayout.allSelectedBasisEquiv
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  have originalDifferent : selection.symm row ≠ label := by
    intro same
    apply different
    exact (selection.apply_symm_apply row).symm.trans
      (congrArg selection same)
  calc
    (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        joint).matrix row column =
      (joint.marginalLeft.reindex selection).matrix row column :=
        congrArg (fun density : DensityOperator
          (ctx.quantumLayout.selectedRegister Finset.univ) =>
            density.matrix row column)
          (DensityOperator.observeSelection_all ctx.quantumLayout Reference joint)
    _ = joint.marginalLeft.matrix (selection.symm row) (selection.symm column) :=
      DensityOperator.reindex_entry joint.marginalLeft selection row column
    _ = ∑ reference : Reference.Index,
          joint.matrix (selection.symm row, reference)
            (selection.symm column, reference) :=
      DensityOperator.marginalLeft_matrix joint _ _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro reference _
      rw [resetToBasis_block_entry (implementations := implementations) outputs label state
        record (selection.symm row) (selection.symm column) reference reference]
      simp only [originalDifferent, false_and, if_false]

end

end QuantumAlg.QuditShift
