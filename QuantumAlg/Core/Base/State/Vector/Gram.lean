/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Normalized

/-!
# Coherent sums with the same Gram matrix

Equality of all pairwise inner products preserves the norm of every finite
coherent linear combination. The basis-label corollary allows collisions on
both sides and preserves their interference terms. It requires neither an
injective branch map nor separately normalized components.
-/

namespace QuantumAlg.HilbertVector

noncomputable section

open scoped BigOperators

/-- The complete inner product of two coherent sums depends only on the Gram matrix. -/
lemma inner_sum_smul_eq_of_gram {R S : Register} {Branch : Type*}
    (indices : Finset Branch) (first : Branch → HilbertVector R)
    (last : Branch → HilbertVector S)
    (same : ∀ left ∈ indices, ∀ right ∈ indices,
      inner ℂ (first left) (first right) = inner ℂ (last left) (last right))
    (leftAmplitude rightAmplitude : Branch → ℂ) :
    inner ℂ (∑ branch ∈ indices, leftAmplitude branch • first branch)
        (∑ branch ∈ indices, rightAmplitude branch • first branch) =
      inner ℂ (∑ branch ∈ indices, leftAmplitude branch • last branch)
        (∑ branch ∈ indices, rightAmplitude branch • last branch) := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro right rightMem
  congr 1
  apply Finset.sum_congr rfl
  intro left leftMem
  rw [same left leftMem right rightMem]

/-- Equal pairwise inner products retain the full norm, including all cross terms. -/
lemma norm_sum_smul_eq_of_gram {R S : Register} {Branch : Type*}
    (indices : Finset Branch) (first : Branch → HilbertVector R)
    (last : Branch → HilbertVector S)
    (same : ∀ left ∈ indices, ∀ right ∈ indices,
      inner ℂ (first left) (first right) = inner ℂ (last left) (last right))
    (amplitude : Branch → ℂ) :
    ‖∑ branch ∈ indices, amplitude branch • first branch‖ =
      ‖∑ branch ∈ indices, amplitude branch • last branch‖ := by
  have squares :
      ‖∑ branch ∈ indices, amplitude branch • first branch‖ ^ 2 =
        ‖∑ branch ∈ indices, amplitude branch • last branch‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_sum_smul_eq_of_gram indices first last same amplitude amplitude]
  nlinarith [norm_nonneg (∑ branch ∈ indices, amplitude branch • first branch),
    norm_nonneg (∑ branch ∈ indices, amplitude branch • last branch)]

private lemma inner_ket {R : Register} (first last : R.Index) :
    inner ℂ (NormalizedVector.ket first : HilbertVector R)
      (NormalizedVector.ket last : HilbertVector R) = if first = last then 1 else 0 := by
  classical
  simp [PiLp.inner_apply, RCLike.inner_apply, NormalizedVector.ket_apply, eq_comm]

/-- The same basis-label collisions preserve every coherent amplitude and its norm. -/
lemma norm_sum_smul_ket_eq_of_eq_iff {R S : Register} {Branch : Type*}
    (indices : Finset Branch) (first : Branch → R.Index) (last : Branch → S.Index)
    (same : ∀ left ∈ indices, ∀ right ∈ indices,
      first left = first right ↔ last left = last right)
    (amplitude : Branch → ℂ) :
    ‖∑ branch ∈ indices,
        amplitude branch • (NormalizedVector.ket (first branch) : HilbertVector R)‖ =
      ‖∑ branch ∈ indices,
        amplitude branch • (NormalizedVector.ket (last branch) : HilbertVector S)‖ := by
  classical
  apply norm_sum_smul_eq_of_gram indices _ _ _ amplitude
  intro left leftMem right rightMem
  simp only [inner_ket, same left leftMem right rightMem]

end

end QuantumAlg.HilbertVector
