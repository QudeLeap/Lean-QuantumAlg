/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.SupportHybrid

/-!
# Coherent geometry of a finite good and bad branch partition

An injective family of computational basis labels has the exact finite
Pythagorean norm. Restricting a normalized expansion to good branches gives
a subnormalized vector, and the omitted vector has exactly the square root
of the bad amplitude mass. No branch measurement or normalization is used.
-/

namespace QuantumAlg.HilbertVector

noncomputable section

variable {R : Register} {Branch : Type*}

/-- Any subfamily of an injective normalized branch expansion has norm at most one. -/
theorem norm_branch_sum_le_one (branches good : Finset Branch) (included : good ⊆ branches)
    (source : Branch → R.Index) (sourceInjective : Function.Injective source)
    (amplitude : Branch → ℂ) (input : NormalizedVector R)
    (expansion : (∑ branch ∈ branches,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)) = input.vec) :
    ‖∑ branch ∈ good,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)‖ ≤ 1 := by
  have totalNorm : Real.sqrt (∑ branch ∈ branches, ‖amplitude branch‖ ^ 2) = 1 :=
    (norm_sum_smul_ket_eq_sqrt_sum_norm_sq branches source sourceInjective amplitude).symm.trans
      ((congrArg norm expansion).trans input.norm_eq_one)
  rw [norm_sum_smul_ket_eq_sqrt_sum_norm_sq good source sourceInjective amplitude, ← totalNorm]
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => sq_nonneg _)

variable [DecidableEq Branch]

/-- A disjoint complete branch partition decomposes the exact coherent input without projection. -/
theorem sub_branch_sum_eq_bad (branches good bad : Finset Branch)
    (partition : good ∪ bad = branches) (disjoint : Disjoint good bad)
    (source : Branch → R.Index) (amplitude : Branch → ℂ) (input : HilbertVector R)
    (expansion : (∑ branch ∈ branches,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)) = input) :
    input - (∑ branch ∈ good,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)) =
      ∑ branch ∈ bad,
        amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R) := by
  rw [← expansion, ← partition, Finset.sum_union disjoint]
  exact add_sub_cancel_left _ _

/-- The omitted coherent vector has exactly the square root of the bad amplitude mass. -/
theorem norm_sub_branch_sum_eq_sqrt_bad (branches good bad : Finset Branch)
    (partition : good ∪ bad = branches) (disjoint : Disjoint good bad)
    (source : Branch → R.Index) (sourceInjective : Function.Injective source)
    (amplitude : Branch → ℂ) (input : HilbertVector R)
    (expansion : (∑ branch ∈ branches,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R)) = input) :
    ‖input - (∑ branch ∈ good,
      amplitude branch • (NormalizedVector.ket (source branch) : HilbertVector R))‖ =
      Real.sqrt (∑ branch ∈ bad, ‖amplitude branch‖ ^ 2) := by
  rw [sub_branch_sum_eq_bad branches good bad partition disjoint source amplitude input expansion]
  exact norm_sum_smul_ket_eq_sqrt_sum_norm_sq bad source sourceInjective amplitude

end

end QuantumAlg.HilbertVector
