/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic

/-!
# Finite matrix Gram identities for a retained mathematical source label

These identities do not define a runtime, allocate a source register, or claim
completeness of an actual point family. The completeness hypotheses are local
linear algebra inputs. A later concrete producer must prove them from the same
actual point operators before any event contraction or success bound follows.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FreeSourceGram

noncomputable section

open scoped BigOperators

/-- Compose two complete matrix families in their actual rightmost-first order. -/
lemma composed_complete {First Second Input Middle Output : Type}
    [Fintype First] [Fintype Second] [Fintype Middle] [Fintype Output]
    [DecidableEq Input] [DecidableEq Middle]
    (first : First → Matrix Middle Input ℂ)
    (second : Second → Matrix Output Middle ℂ)
    (firstComplete : ∑ label, (first label).conjTranspose * first label = 1)
    (secondComplete : ∑ label, (second label).conjTranspose * second label = 1) :
    ∑ left, ∑ right, (second right * first left).conjTranspose *
      (second right * first left) = 1 := by
  calc
    _ = ∑ left, (first left).conjTranspose *
        (∑ right, (second right).conjTranspose * second right) * first left := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = ∑ left, (first left).conjTranspose * first left := by
      simp only [secondComplete, Matrix.mul_one]
    _ = 1 := firstComplete

/-- Keeping the source label makes completeness a separate fact in each block. -/
lemma source_preserving_complete {Outcome Source Bank : Type}
    [Fintype Outcome] [Fintype Source] [Fintype Bank]
    [DecidableEq Source] [DecidableEq Bank]
    (kernel : Outcome → Source → Matrix Bank Bank ℂ)
    (complete : ∀ source, ∑ outcome,
      (kernel outcome source).conjTranspose * kernel outcome source = 1) :
    ∑ outcome, (Matrix.blockDiagonal (kernel outcome)).conjTranspose *
      Matrix.blockDiagonal (kernel outcome) = 1 := by
  calc
    _ = ∑ outcome, Matrix.blockDiagonal (fun source =>
        (kernel outcome source).conjTranspose * kernel outcome source) := by
      simp only [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    _ = Matrix.blockDiagonal (fun source => ∑ outcome,
        (kernel outcome source).conjTranspose * kernel outcome source) := by
      ext ⟨row, source⟩ ⟨column, other⟩
      by_cases same : source = other
      · simp only [Matrix.sum_apply, Matrix.blockDiagonal_apply, if_pos same]
      · simp only [Matrix.sum_apply, Matrix.blockDiagonal_apply, if_neg same,
          Finset.sum_const_zero]
    _ = 1 := by
      have diagonal : (fun source => ∑ outcome,
          (kernel outcome source).conjTranspose * kernel outcome source) =
          (1 : Source → Matrix Bank Bank ℂ) := funext complete
      rw [diagonal, Matrix.blockDiagonal_one]

/-- An outcome-selected unitary suffix preserves the Gram sum of the measured family. -/
lemma selected_suffix_complete {Outcome Bank : Type}
    [Fintype Outcome] [Fintype Bank] [DecidableEq Bank]
    (before : Matrix Bank Bank ℂ) (measured suffix : Outcome → Matrix Bank Bank ℂ)
    (beforeComplete : before.conjTranspose * before = 1)
    (measuredComplete : ∑ outcome,
      (measured outcome).conjTranspose * measured outcome = 1)
    (suffixComplete : ∀ outcome,
      (suffix outcome).conjTranspose * suffix outcome = 1) :
    ∑ outcome, (suffix outcome * measured outcome * before).conjTranspose *
      (suffix outcome * measured outcome * before) = 1 := by
  calc
    _ = ∑ outcome, before.conjTranspose *
        ((measured outcome).conjTranspose *
          ((suffix outcome).conjTranspose * suffix outcome) * measured outcome) * before := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = before.conjTranspose *
        (∑ outcome, (measured outcome).conjTranspose * measured outcome) * before := by
      simp only [suffixComplete, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = 1 := by rw [measuredComplete, Matrix.mul_one, beforeComplete]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FreeSourceGram
