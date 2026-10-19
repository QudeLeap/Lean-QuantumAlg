/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Owned.Borrowed.CoordinateAgreement
import all QuantumAlg.Core.Execution.Owned.Borrowed.Coordinates
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Pure.MarginalCoordinates
import all QuantumAlg.Core.Execution.Measurement.Selection
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Borrowed joint observations forced by an actual local pure tensor

An actual local pure tensor fixes the borrowed state jointly with the
original reference. Summing the owned coordinates removes only their
normalized pure factor. The reference factor is read from the same joint
density; no product-state assumption is supplied for that density.
-/

namespace QuantumAlg.Execution.OwnedBorrowedQubits

noncomputable section

/-- A local pure tensor fixes every borrowed-reference coherence of the actual execution. -/
lemma observeBorrowed_pureTensor_entry (owned borrowed : Nat)
    [Subsingleton (context owned borrowed).borrowedClassicalShape.Value]
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (context owned borrowed) Reference H)
    (ownedState : NormalizedVector (Qubits owned))
    (borrowedState : NormalizedVector (Qubits borrowed))
    (promised : state.quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (ownedState.tensor borrowedState)).reindex
        (S := (context owned borrowed).register) (basisEquiv owned borrowed).symm)
    (value : (context owned borrowed).borrowedClassicalShape.Value)
    (row column : (context owned borrowed).borrowedQuantumLayout.Basis)
    (refRow refColumn : Reference.Index) :
    ((observeBorrowed Reference state).block value).matrix (row, refRow) (column, refColumn) =
      (borrowedState (borrowedBinaryEquiv owned borrowed
          ((context owned borrowed).borrowedBasisEquiv.symm row)) *
        star (borrowedState (borrowedBinaryEquiv owned borrowed
          ((context owned borrowed).borrowedBasisEquiv.symm column)))) *
        ∑ index : (context owned borrowed).register.Index,
          state.quantumMarginal.matrix (index, refRow) (index, refColumn) := by
  rw [observeBorrowed_block_of_subsingleton, RuntimeCtx.observeBorrowedWithReference_entry]
  let reference := ∑ index : (context owned borrowed).register.Index,
    state.quantumMarginal.matrix (index, refRow) (index, refColumn)
  let source := borrowedState (borrowedBinaryEquiv owned borrowed
      ((context owned borrowed).borrowedBasisEquiv.symm row)) *
    star (borrowedState (borrowedBinaryEquiv owned borrowed
      ((context owned borrowed).borrowedBasisEquiv.symm column)))
  have normalized : (∑ complement : (context owned borrowed).quantumLayout.ComplementBasis
      (context owned borrowed).borrowedSelection,
        ownedState (ownedBinaryEquiv owned borrowed complement) *
          star (ownedState (ownedBinaryEquiv owned borrowed complement))) = 1 :=
    ((ownedBinaryEquiv owned borrowed).sum_comp
      (fun index => ownedState index * star (ownedState index))).trans
        (DensityOperator.trace_pureMatrix ownedState)
  calc
    _ = ∑ complement : (context owned borrowed).quantumLayout.ComplementBasis
        (context owned borrowed).borrowedSelection,
      ((ownedState.tensor borrowedState)
          (basisEquiv owned borrowed
            ((context owned borrowed).quantumLayout.joinSelectedBasis
              (context owned borrowed).borrowedSelection
              ((context owned borrowed).borrowedBasisEquiv.symm row) complement)) *
        star ((ownedState.tensor borrowedState)
          (basisEquiv owned borrowed
            ((context owned borrowed).quantumLayout.joinSelectedBasis
              (context owned borrowed).borrowedSelection
              ((context owned borrowed).borrowedBasisEquiv.symm column) complement)))) *
        reference := by
      apply Finset.sum_congr rfl
      intro complement _
      exact DensityOperator.pureMarginal_reindexed_entry state.quantumMarginal
        (basisEquiv owned borrowed) (ownedState.tensor borrowedState) promised _ _ refRow refColumn
    _ = (source * reference) * ∑ complement :
        (context owned borrowed).quantumLayout.ComplementBasis
          (context owned borrowed).borrowedSelection,
      ownedState (ownedBinaryEquiv owned borrowed complement) *
        star (ownedState (ownedBinaryEquiv owned borrowed complement)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro complement _
      rw [basisEquiv_join, basisEquiv_join,
        NormalizedVector.tensor_apply_prod, NormalizedVector.tensor_apply_prod]
      simp only [star_mul]
      dsimp only [source]
      ring
    _ = _ := by rw [normalized, mul_one]

/-- Changing only the owned pure factor preserves the full borrowed observation when
the actual external-reference marginal remains equal. -/
lemma observeBorrowed_pureTensor_eq (owned borrowed : Nat)
    [Subsingleton (context owned borrowed).borrowedClassicalShape.Value]
    {Reference : Register} {H K : Type} [Fintype H] [Fintype K]
    (initial : State (context owned borrowed) Reference H)
    (finalState : State (context owned borrowed) Reference K)
    (initialOwned finalOwned : NormalizedVector (Qubits owned))
    (borrowedState : NormalizedVector (Qubits borrowed))
    (initialPure : initial.quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (initialOwned.tensor borrowedState)).reindex
        (S := (context owned borrowed).register) (basisEquiv owned borrowed).symm)
    (finalPure : finalState.quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (finalOwned.tensor borrowedState)).reindex
        (S := (context owned borrowed).register) (basisEquiv owned borrowed).symm)
    (sameReference : ∀ refRow refColumn : Reference.Index,
      (∑ index : (context owned borrowed).register.Index,
        finalState.quantumMarginal.matrix (index, refRow) (index, refColumn)) =
      ∑ index : (context owned borrowed).register.Index,
        initial.quantumMarginal.matrix (index, refRow) (index, refColumn)) :
    observeBorrowed Reference finalState = observeBorrowed Reference initial := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, refLeft⟩
  rcases column with ⟨right, refRight⟩
  rw [observeBorrowed_pureTensor_entry owned borrowed finalState finalOwned borrowedState finalPure,
    observeBorrowed_pureTensor_entry owned borrowed initial initialOwned borrowedState initialPure,
    sameReference]

end

end QuantumAlg.Execution.OwnedBorrowedQubits
