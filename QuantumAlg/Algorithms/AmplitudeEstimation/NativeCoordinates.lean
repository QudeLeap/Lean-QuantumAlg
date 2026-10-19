/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Context
import all QuantumAlg.Algorithms.AmplitudeEstimation.Storage
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.ProgramLaws
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Original source coordinates when no extra work system is present

The original admitted parameter domain has no additional work system. This
leaf compares the actual runtime basis, its zero preparation, full operator,
and phase readout with the original source coordinates. Every equivalence
preserves the numeric basis value; no physical wire is discarded or added.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

open QuantumAlg.Execution

/-- The actual prepared basis, expressed at the original source width. -/
def preparedOriginalBasisEquiv (t n : Nat) (empty : Elementary.helperWidth t n = 0) :
    (preparedContext t n).register.Index ≃ (Qubits (t + n)).Index :=
  (preparedBasisEquiv t n).trans (finCongr (congrArg (fun width : Nat => 2 ^ width)
    (by rw [empty, Nat.zero_add])))

/-- The same basis after actual retained-cell allocations. -/
def outputOriginalBasisEquiv (t n : Nat) (empty : Elementary.helperWidth t n = 0) :
    (post t n).register.Index ≃ (Qubits (t + n)).Index :=
  (MeasurementCells.basisEquiv (resultContext t n) 2 t).symm.trans
    (preparedOriginalBasisEquiv t n empty)

private lemma allZeroInput_eq_ket {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) :
    allZeroInput E t = NormalizedVector.ket (R := Qubits (t + n)) 0 := by
  rw [allZeroInput, IntrinsicAmplitudeAmplificationModel.zeroKet,
    NormalizedVector.tensor_ket]
  rfl

/-- The actual full zero preparation agrees with the source input in these exact coordinates. -/
lemma inputPreparation_density_original {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (empty : Elementary.helperWidth t n = 0) :
    (DensityOperator.ofPure (inputPreparation t n).normalized).reindex
      (S := (preparedContext t n).register) (preparedLayoutEquiv t n) =
        (DensityOperator.ofPure (allZeroInput E t)).reindex
          (S := (preparedContext t n).register) (preparedOriginalBasisEquiv t n empty).symm := by
  rw [inputPreparation_density]
  have value (basis : (preparedContext t n).register.Index) :
      preparedInput t n (preparedBasisEquiv t n basis) =
        allZeroInput E t (preparedOriginalBasisEquiv t n empty basis) := by
    rw [allZeroInput_eq_ket]
    have zero : preparedBasisEquiv t n basis = 0 ↔
        preparedOriginalBasisEquiv t n empty basis = 0 := by
      rw [Fin.ext_iff, Fin.ext_iff]
      rfl
    simp only [preparedInput, NormalizedVector.ket_apply, zero]
  apply DensityOperator.ext
  ext row column
  rw [DensityOperator.reindex_entry, DensityOperator.reindex_entry,
    DensityOperator.ofPure_matrix, DensityOperator.ofPure_matrix]
  simp only [Equiv.symm_symm, value]

private lemma preparedLayoutEquiv_eq_wireBasis (t n : Nat) :
    preparedLayoutEquiv t n =
      basisOfEqualWires
        (runtimeLayout t n)
        (preparedContext t n).quantumLayout (prepared_canonical_wires t n) := by
  apply Equiv.ext
  intro basis
  funext target
  let layout :=
    (runtimeLayout t n)
  obtain ⟨index, rfl⟩ :=
    (positionsOfEqualWires layout (preparedContext t n).quantumLayout
      (prepared_canonical_wires t n)).surjective
      target
  apply Fin.ext
  have position :
      positionsOfEqualWires layout (preparedContext t n).quantumLayout
        (prepared_canonical_wires t n) index =
        pre.addOwnedLayoutPositionEquiv ⟨0⟩ (runtimeLayout t n) preparationFresh
          (preparationDisjoint t n) (Fin.castAdd pre.systemCount index) := by
    apply Fin.ext
    rfl
  have prepared :
      (preparedLayoutEquiv t n basis
        (positionsOfEqualWires layout (preparedContext t n).quantumLayout
          (prepared_canonical_wires t n) index)).val = (basis index).val := by
    rw [position]
    exact (pre.addOwnedLayout_basis_value_preserved ⟨0⟩ (runtimeLayout t n)
      preparationFresh (preparationDisjoint t n) _ (Fin.castAdd pre.systemCount index)).trans
        (QuantumLayout.appendJoinBasis_left_value _ _ _ basis
          (emptyContextBasis pre pre_systemCount) index)
  exact prepared.trans
    (basisOfEqualWires_value layout (preparedContext t n).quantumLayout
      (prepared_canonical_wires t n) basis index).symm

private lemma nativeProgram_matrix {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) :
    ((nativeProgram n t).matrix (AmplitudeAmplificationSource.interpretation E.source.preparation
      E.source.good true true)) =
      UnitaryOperator.reindex (preparedBasisEquiv t n).symm ((runtimeProgram n t).binaryMatrix
        (AmplitudeAmplificationSource.interpretation E.source.preparation E.source.good true true))
        := by
  rw [nativeProgram, unitaryOfEqualWires_matrix, UnitaryCircuit.binaryMatrix,
    UnitaryOperator.unitaryOperator_reindex_trans]
  rw [preparedBasisEquiv, preparedLayoutEquiv_eq_wireBasis]
  exact congrArg (fun equivalence => UnitaryOperator.reindex equivalence
    ((runtimeProgram n t).matrix (AmplitudeAmplificationSource.interpretation E.source.preparation
      E.source.good true true))) (by
      apply Equiv.ext
      intro basis
      simp only [Equiv.symm_trans_apply, Equiv.trans_apply]
      apply congrArg (basisOfEqualWires (runtimeLayout t n)
        (preparedContext t n).quantumLayout (prepared_canonical_wires t n))
      exact ((QuantumSignature.qubitsIndexEquiv
        (t + (Elementary.helperWidth t n + n))).symm_apply_apply basis).symm)

/-- The actual elementary circuit has the independent source operator on every basis value. -/
lemma nativeProgram_matrix_original {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (t : Nat) (empty : Elementary.helperWidth t n = 0) :
    ((nativeProgram n t).matrix (AmplitudeAmplificationSource.interpretation E.source.preparation
      E.source.good true true)) = UnitaryOperator.reindex
      (preparedOriginalBasisEquiv t n empty).symm (sourceOperator E t) := by
  calc
    _ = UnitaryOperator.reindex (preparedOriginalBasisEquiv t n empty).symm
        (UnitaryOperator.reindex (Elementary.unextendedBasisEquiv t n empty)
          ((Elementary.program n t).binaryMatrix (AmplitudeAmplificationSource.interpretation
            E.source.preparation E.source.good true true))) := by
      apply Subtype.ext
      ext row column
      rw [nativeProgram_matrix, runtimeProgram, Elementary.castCircuit_matrix]
      simp only [UnitaryOperator.coe_reindex,
        Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
      congr 1
    _ = _ := by
      rw [Elementary.program_matrix_of_noHelper,
        QuantumPhaseEstimation.Native.qpeNative_circuit_binaryMatrix]
      rfl

/-- The actual phase readout is the original readout, with each phase bit preserved. -/
lemma phaseReadout_original (t n : Nat) (empty : Elementary.helperWidth t n = 0)
    (basis : (post t n).register.Index) :
    (qpeMeasurement t (Elementary.helperWidth t n + n)).readout (outputBasisEquiv t n basis) =
      (qpeMeasurement t n).readout (outputOriginalBasisEquiv t n empty basis) := by
  funext index
  change (outputBasisEquiv t n basis).val.testBit
      (t + (Elementary.helperWidth t n + n) - 1 - index.val) =
    (outputOriginalBasisEquiv t n empty basis).val.testBit (t + n - 1 - index.val)
  have value : (outputOriginalBasisEquiv t n empty basis).val =
      (outputBasisEquiv t n basis).val := rfl
  have position : t + (Elementary.helperWidth t n + n) - 1 - index.val =
      t + n - 1 - index.val := by rw [empty, Nat.zero_add]
  exact congrArg₂ Nat.testBit value.symm position

end

end QuantumAlg.AmplitudeEstimation
