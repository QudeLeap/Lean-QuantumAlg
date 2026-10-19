/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic

/-!
# Orthogonal frequency columns and complete source-indexed Kraus families

Frequency orthogonality removes the cross-source Gram entries. Completeness
within each source then gives the identity on the full source-times-bank space.
No orthogonality between Kraus families at different sources is assumed.

These are generic matrix identities. The concrete frequency rows, complete
Kraus words, and their identification with actual legal execution labels remain
separate internal proof obligations. No runtime or algorithm caller condition
is introduced, and no actual execution completeness or success floor is claimed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace FourierKrausCompleteness

noncomputable section

open scoped BigOperators

variable {Source Frequency Outcome Bank : Type}

/-- The source coordinate remains a separate column beside the entire bank. -/
def columns (frequencyRows : Frequency → Source → ℂ)
    (kernels : Outcome → Source → Matrix Bank Bank ℂ)
    (frequency : Frequency) (outcome : Outcome) : Matrix Bank (Source × Bank) ℂ :=
  fun output input => frequencyRows frequency input.1 * kernels outcome input.1 output input.2

/-- Every Gram entry factors into a frequency inner product and a cross-source Kraus sum. -/
lemma columns_gram_entry [Fintype Frequency] [Fintype Outcome] [Fintype Bank]
    (frequencyRows : Frequency → Source → ℂ)
    (kernels : Outcome → Source → Matrix Bank Bank ℂ)
    (source target : Source) (column other : Bank) :
    (∑ frequency, ∑ outcome,
      (columns frequencyRows kernels frequency outcome).conjTranspose *
        columns frequencyRows kernels frequency outcome) (source, column) (target, other) =
      (∑ frequency, star (frequencyRows frequency source) * frequencyRows frequency target) *
        (∑ outcome, ((kernels outcome source).conjTranspose *
          kernels outcome target) column other) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, columns]
  calc
    (∑ frequency, ∑ outcome, ∑ row,
      star (frequencyRows frequency source * kernels outcome source row column) *
        (frequencyRows frequency target * kernels outcome target row other)) =
        ∑ frequency, ∑ outcome, ∑ row,
          (star (frequencyRows frequency source) * frequencyRows frequency target) *
            (star (kernels outcome source row column) * kernels outcome target row other) := by
      apply Finset.sum_congr rfl
      intro frequency _
      apply Finset.sum_congr rfl
      intro outcome _
      apply Finset.sum_congr rfl
      intro row _
      rw [star_mul]
      ring
    _ = (∑ frequency,
        star (frequencyRows frequency source) * frequencyRows frequency target) *
        (∑ outcome, ∑ row,
          star (kernels outcome source row column) * kernels outcome target row other) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro outcome _
      rw [Finset.sum_comm]

/-- Orthogonal frequency columns and each source's complete Kraus family give full completeness. -/
lemma columns_complete [Fintype Frequency] [Fintype Outcome] [Fintype Bank]
    [DecidableEq Source] [DecidableEq Bank]
    (frequencyRows : Frequency → Source → ℂ)
    (kernels : Outcome → Source → Matrix Bank Bank ℂ)
    (orthogonal : ∀ source target,
      (∑ frequency, star (frequencyRows frequency source) * frequencyRows frequency target) =
        if source = target then 1 else 0)
    (complete : ∀ source,
      ∑ outcome, (kernels outcome source).conjTranspose * kernels outcome source = 1) :
    ∑ frequency, ∑ outcome,
      (columns frequencyRows kernels frequency outcome).conjTranspose *
        columns frequencyRows kernels frequency outcome = 1 := by
  ext ⟨source, column⟩ ⟨target, other⟩
  rw [columns_gram_entry, orthogonal]
  by_cases same : source = target
  · subst target
    have entry := congrArg (fun matrix : Matrix Bank Bank ℂ => matrix column other)
      (complete source)
    rw [if_pos rfl, one_mul]
    calc
      (∑ outcome, ((kernels outcome source).conjTranspose *
          kernels outcome source) column other) = (1 : Matrix Bank Bank ℂ) column other := by
        simpa only [Matrix.sum_apply] using entry
      _ = (1 : Matrix (Source × Bank) (Source × Bank) ℂ)
          (source, column) (source, other) := by
        by_cases sameColumn : column = other
        · subst other
          simp only [Matrix.one_apply_eq]
        · have distinct : (source, column) ≠ (source, other) := by
            intro equality
            exact sameColumn (congrArg Prod.snd equality)
          rw [Matrix.one_apply_ne sameColumn, Matrix.one_apply_ne distinct]
  · have distinct : (source, column) ≠ (target, other) := by
      intro equality
      exact same (congrArg Prod.fst equality)
    rw [if_neg same, zero_mul, Matrix.one_apply_ne distinct]

end

end FourierKrausCompleteness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
