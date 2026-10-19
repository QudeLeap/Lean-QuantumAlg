/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Cascade
import Mathlib.Data.Matrix.Block

/-!
# Coherent contraction of one actual arithmetic measurement path

These are finite matrix laws on the fixed bank-first coordinates of the actual old
cascade. They do not assert that an arbitrary old input is prepared or that a
mathematical row is an actual Fourier readout. The physical preparation/readout
identities remain separate. Different arithmetic paths are never summed as amplitudes.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured.CommonBank.CoherentContraction

noncomputable section

open QuantumAlg QuantumAlg.Execution
open scoped BigOperators

variable {Exponent Arithmetic : Type}
  [Fintype Exponent] [Fintype Arithmetic] [DecidableEq Exponent] [DecidableEq Arithmetic]

/-- Coherent exponent amplitudes beside an arbitrary unchanged bank column. -/
def preparedColumns (amplitude : Exponent → ℂ) : Matrix (Arithmetic × Exponent) Arithmetic ℂ :=
  fun row column => amplitude row.2 * (if row.1 = column then 1 else 0)

/-- A fixed output exponent beside the complete unchanged bank, with no trace operation. -/
def outputColumns (output : Exponent) : Matrix (Arithmetic × Exponent) Arithmetic ℂ :=
  fun row column => if row.2 = output ∧ row.1 = column then 1 else 0

/-- One mathematical rank-one row on the exponent, tensored with literal bank identity. -/
def readoutKernel (output : Exponent) (rowCoefficient : Exponent → ℂ) :
    Matrix (Arithmetic × Exponent) (Arithmetic × Exponent) ℂ :=
  fun row column =>
    if row.2 = output ∧ row.1 = column.1 then rowCoefficient column.2 else 0

/-- Coherent contraction stays inside one measured arithmetic branch. -/
def weightedWord (amplitude rowCoefficient : Exponent → ℂ)
    (operators : Exponent → Matrix Arithmetic Arithmetic ℂ) :
    Matrix Arithmetic Arithmetic ℂ :=
  ∑ exponent, (rowCoefficient exponent * amplitude exponent) • operators exponent

private lemma blockDiagonal_prepared_entry
    (amplitude : Exponent → ℂ) (operators : Exponent → Matrix Arithmetic Arithmetic ℂ)
    (row : Arithmetic × Exponent) (column : Arithmetic) :
    (Matrix.blockDiagonal operators * preparedColumns (Arithmetic := Arithmetic) amplitude)
      row column =
      amplitude row.2 * operators row.2 row.1 column := by
  simp [Matrix.mul_apply, Matrix.blockDiagonal_apply, preparedColumns,
    Fintype.sum_prod_type, mul_comm]

/-- No exponent dephasing is used: every coherent input term contributes to the same bank word. -/
lemma readout_diagonal_prepared
    (output : Exponent) (amplitude rowCoefficient : Exponent → ℂ)
    (operators : Exponent → Matrix Arithmetic Arithmetic ℂ) :
    readoutKernel (Arithmetic := Arithmetic) output rowCoefficient *
        (Matrix.blockDiagonal operators * preparedColumns (Arithmetic := Arithmetic) amplitude) =
      outputColumns (Arithmetic := Arithmetic) output *
        weightedWord amplitude rowCoefficient operators := by
  ext row column
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [blockDiagonal_prepared_entry]
  by_cases selected : row.2 = output
  · simp [readoutKernel, outputColumns, weightedWord, selected,
      Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply,
      mul_comm, mul_left_comm]
  · simp [readoutKernel, outputColumns, selected]

/-- One path's complete conditional bank state retains arbitrary mixed Reference correlations. -/
lemma readout_diagonal_prepared_sandwich
    (output : Exponent) (amplitude rowCoefficient : Exponent → ℂ)
    (operators : Exponent → Matrix Arithmetic Arithmetic ℂ)
    (density : Matrix Arithmetic Arithmetic ℂ) :
    readoutKernel (Arithmetic := Arithmetic) output rowCoefficient *
        (Matrix.blockDiagonal operators *
          (preparedColumns (Arithmetic := Arithmetic) amplitude * density *
            (preparedColumns (Arithmetic := Arithmetic) amplitude).conjTranspose) *
          (Matrix.blockDiagonal operators).conjTranspose) *
        (readoutKernel (Arithmetic := Arithmetic) output rowCoefficient).conjTranspose =
      outputColumns (Arithmetic := Arithmetic) output *
        (weightedWord amplitude rowCoefficient operators * density *
          (weightedWord amplitude rowCoefficient operators).conjTranspose) *
        (outputColumns (Arithmetic := Arithmetic) output).conjTranspose := by
  calc
    _ = (readoutKernel (Arithmetic := Arithmetic) output rowCoefficient *
          (Matrix.blockDiagonal operators * preparedColumns (Arithmetic := Arithmetic) amplitude)) *
        density *
        (readoutKernel (Arithmetic := Arithmetic) output rowCoefficient *
          (Matrix.blockDiagonal operators *
            preparedColumns (Arithmetic := Arithmetic) amplitude)).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (outputColumns (Arithmetic := Arithmetic) output *
          weightedWord amplitude rowCoefficient operators) * density *
        (outputColumns (Arithmetic := Arithmetic) output *
          weightedWord amplitude rowCoefficient operators).conjTranspose := by
      rw [readout_diagonal_prepared]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end Measured.CommonBank.CoherentContraction
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
