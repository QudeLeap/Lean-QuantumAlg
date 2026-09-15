/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.QPE.Context
import all QuantumAlg.Algorithms.QPE.Execution
import all QuantumAlg.Algorithms.QPE.Specification
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Execution.Owned.Borrowed.Preparation
import all QuantumAlg.Core.Execution.Owned.Borrowed.Qubits
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.State.Normalized

/-!
# The actual phase-prefix preparation on the promised borrowed eigenstate

The single interpreter prepares only the phase word. Its tensor-entry law
and the promised original local eigenstate give the exact source input
density. The external reference is traced only for this local observation;
all reference coherences remain in the actual joint execution state.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

open QuantumAlg.Execution

private theorem preparation_basis_value (t : Nat) (basis : (phaseRuntimeLayout t).Basis) :
    (inputPreparation t).normalized basis =
      NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t))
        ((OwnedBorrowedQubits.wordLayout t).binaryIndexEquiv basis) := by
  change NormalizedVector.ket
    ((OwnedBorrowedQubits.wordLayout t).binaryIndexEquiv.symm (0 : Fin (2 ^ t))) basis = _
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  simp only [Equiv.eq_symm_apply]

private theorem preparation_basis_encoding (t n : Nat)
    (newBasis : (phaseRuntimeLayout t).register.Index) (oldBasis : (pre t n).register.Index) :
    preparedBasisEquiv t n (OwnedBorrowedQubits.preparationBasisEquiv t n (newBasis, oldBasis)) =
      prodEquiv ((OwnedBorrowedQubits.wordLayout t).binaryIndexEquiv newBasis,
        inputBasisEquiv t n oldBasis) :=
  OwnedBorrowedQubits.basisEquiv_preparation t n newBasis oldBasis

private theorem source_input_entry {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (newRow newColumn : (phaseRuntimeLayout t).register.Index)
    (oldRow oldColumn : (pre t n).register.Index) :
    ((DensityOperator.ofPure (qpeInput P t)).reindex
      (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm).matrix
        (OwnedBorrowedQubits.preparationBasisEquiv t n (newRow, oldRow))
        (OwnedBorrowedQubits.preparationBasisEquiv t n (newColumn, oldColumn)) =
      ((inputPreparation t).normalized newRow *
          star ((inputPreparation t).normalized newColumn)) *
        (P.eigenstate (inputBasisEquiv t n oldRow) *
          star (P.eigenstate (inputBasisEquiv t n oldColumn))) := by
  have inputValue (newBasis : (phaseRuntimeLayout t).register.Index)
      (oldBasis : (pre t n).register.Index) :
      qpeInput P t
          (preparedBasisEquiv t n
            (OwnedBorrowedQubits.preparationBasisEquiv t n (newBasis, oldBasis))) =
        (inputPreparation t).normalized newBasis *
          P.eigenstate (inputBasisEquiv t n oldBasis) := by
    calc
      _ = qpeInput P t
          (prodEquiv ((OwnedBorrowedQubits.wordLayout t).binaryIndexEquiv newBasis,
            inputBasisEquiv t n oldBasis)) :=
        congrArg (fun index : Fin (2 ^ (t + n)) => qpeInput P t index)
          (preparation_basis_encoding t n newBasis oldBasis)
      _ = _ := by
        rw [qpeInput, NormalizedVector.tensor_apply_prod, preparation_basis_value]
  rw [DensityOperator.reindex_entry, DensityOperator.ofPure_matrix]
  simp only [Equiv.symm_symm]
  calc
    _ = ((inputPreparation t).normalized newRow *
          P.eigenstate (inputBasisEquiv t n oldRow)) *
        star ((inputPreparation t).normalized newColumn *
          P.eigenstate (inputBasisEquiv t n oldColumn)) :=
      congrArg₂ (fun left right : ℂ => left * star right)
        (inputValue newRow oldRow) (inputValue newColumn oldColumn)
    _ = _ := by
      rw [star_mul]
      ring

/-- The actual phase preparation yields precisely the original zero-phase/eigenstate input. -/
theorem preparationCode_localDensity {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    {Reference : Register} {H : Type} [Fintype H] (state : State (pre t n) Reference H)
    (promised : inputPromise P t state.quantumMarginal.marginalLeft) :
    ((preparationCode t n).execute Reference state).quantumMarginal.marginalLeft =
      (DensityOperator.ofPure (qpeInput P t)).reindex
        (S := (preparedContext t n).register) (preparedBasisEquiv t n).symm := by
  apply DensityOperator.ext
  ext row column
  obtain ⟨⟨newRow, oldRow⟩, rfl⟩ := (OwnedBorrowedQubits.preparationBasisEquiv t n).surjective row
  obtain ⟨⟨newColumn, oldColumn⟩, rfl⟩ :=
    (OwnedBorrowedQubits.preparationBasisEquiv t n).surjective column
  rw [source_input_entry]
  calc
    _ = ∑ reference : Reference.Index,
        ((preparationCode t n).execute Reference state).quantumMarginal.matrix
          (OwnedBorrowedQubits.preparationBasisEquiv t n (newRow, oldRow), reference)
          (OwnedBorrowedQubits.preparationBasisEquiv t n (newColumn, oldColumn), reference) :=
      DensityOperator.marginalLeft_matrix _ _ _
    _ = ∑ reference : Reference.Index,
        ((inputPreparation t).normalized newRow *
          star ((inputPreparation t).normalized newColumn)) *
          state.quantumMarginal.matrix (oldRow, reference) (oldColumn, reference) := by
      apply Finset.sum_congr rfl
      intro reference _
      exact Circuit.prepare_joined_entry state ⟨0⟩ (phaseRuntimeLayout t)
        (preparationFresh t n) (preparationDisjoint t n) (inputPreparation t)
        newRow newColumn (oldRow, reference) (oldColumn, reference)
    _ = ((inputPreparation t).normalized newRow *
          star ((inputPreparation t).normalized newColumn)) *
        state.quantumMarginal.marginalLeft.matrix oldRow oldColumn := by
      rw [← Finset.mul_sum]
      exact congrArg
        (fun value : ℂ =>
          ((inputPreparation t).normalized newRow *
          star ((inputPreparation t).normalized newColumn)) *
            value)
        (DensityOperator.marginalLeft_matrix (R := (pre t n).register) (S := Reference)
          state.quantumMarginal oldRow oldColumn).symm
    _ = _ := congrArg
      (fun value : ℂ =>
        ((inputPreparation t).normalized newRow *
          star ((inputPreparation t).normalized newColumn)) *
          value) (promised oldRow oldColumn)

end

end QuantumAlg.QuantumPhaseEstimation
