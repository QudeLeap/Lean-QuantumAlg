/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Cleanup
import all QuantumAlg.Components.Classical.Model.BitWord
import all QuantumAlg.Core.Execution.Pure.Point
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.Restart

/-!
# Every actual whole-bank cleanup record has the same zero seed

The full executed block includes the actual reused-cell writes, service
state, incoming history and complete MZ/correction paths. No validity or
good-prefix promise is needed, including on zero-weight output records.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Cleanup.Parameters

noncomputable section

open Execution

private instance reinitializedDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Cleanup.Parameters ctx)

def zeroLabel (_parameters : Cleanup.Parameters ctx) : ctx.quantumLayout.Basis := fun _ => 0

lemma circuit_zero_row
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × (services.HiddenState ×
      (History × (parameters.circuit (services := services)).Path)))
    (left right : ctx.quantumLayout.Basis) (refLeft refRight : Reference.Index)
    (different : left ≠ parameters.zeroLabel) :
    ((parameters.circuit.execute environment Reference state).block record).matrix
      (left, refLeft) (right, refRight) = 0 := by
  obtain ⟨wire, outside⟩ : ∃ wire, left wire ≠ 0 := by
    by_contra absent
    push Not at absent
    exact different (funext absent)
  exact parameters.run_supported environment ctx.systemCount id state wire
    record left right refLeft refRight outside

/-- Every full actual record has pure zero on the complete original physical bank. -/
lemma circuit_pure_fullSelection
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (record : Store ctx × (services.HiddenState ×
      (History × (parameters.circuit (services := services)).Path))) :
    (StatePromise.pure (NormalizedVector.ket
      (R := ctx.quantumLayout.selectedRegister Finset.univ)
      (ctx.quantumLayout.restrictSelectedBasis Finset.univ parameters.zeroLabel))).Holds
        (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
          ((parameters.circuit.execute environment Reference state).block record)) := by
  let joint := (parameters.circuit.execute environment Reference state).block record
  let selection : ctx.register.Index ≃
      (ctx.quantumLayout.selectedRegister Finset.univ).Index := by
    change ctx.quantumLayout.Basis ≃ ctx.quantumLayout.SelectedBasis Finset.univ
    exact ctx.quantumLayout.allSelectedBasisEquiv
  apply StatePromise.statePromise_pureKet_of_row_support
  intro row different column
  have originalDifferent : selection.symm row ≠ parameters.zeroLabel := by
    intro same
    apply different
    exact (selection.apply_symm_apply row).symm.trans (congrArg selection same)
  calc
    (DensityOperator.observeSelection ctx.quantumLayout Finset.univ Reference
        joint).matrix row column =
      (joint.marginalLeft.reindex selection).matrix row column :=
        congrArg (fun density : DensityOperator
          (ctx.quantumLayout.selectedRegister Finset.univ) => density.matrix row column)
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
      exact parameters.circuit_zero_row environment state record
        (selection.symm row) (selection.symm column) reference reference originalDifferent

/-- On the fully owned bank the literal cleanup reinitializes every reachable record. -/
lemma circuit_reinitializedAt
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt parameters.circuit environment
      (ctx.quantumLayout.restrictSelectedBasis ctx.borrowedSelectionᶜ parameters.zeroLabel) := by
  have empty : ctx.borrowedSelection = ∅ := by
    ext wire
    simp only [RuntimeCtx.mem_borrowedSelection, noBorrowed, List.not_mem_nil,
      Finset.notMem_empty]
  have all : ctx.borrowedSelectionᶜ = Finset.univ := by simp only [empty, Finset.compl_empty]
  unfold Circuit.ReinitializedAt
  rw [all]
  intro Reference History _ state record
  exact parameters.circuit_pure_fullSelection environment state record

end

end Cleanup.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
