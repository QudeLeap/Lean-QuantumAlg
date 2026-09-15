/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Computational-basis support hybrids

This module bounds the distance between two unitary evolutions that agree on
all computational-basis labels outside one explicit finite exceptional set.
The estimate is stated for raw Hilbert vectors, because the good and bad
support components need not be normalized separately.
-/

section

namespace QuantumAlg

noncomputable section

namespace HilbertVector

/-- Every finite-dimensional state is the sum of its computational-basis
amplitudes times the corresponding basis kets. -/
theorem sum_amplitude_smul_ket {R : Register} (state : HilbertVector R) :
    (∑ index : R.Index,
      state index • (NormalizedVector.ket index : HilbertVector R)) = state := by
  apply WithLp.ofLp_injective
  funext output
  simp [NormalizedVector.ket_apply]

/-- Distinct computational-basis labels give the usual Pythagorean norm for a
finite linear combination of basis kets. -/
theorem norm_sum_smul_ket_eq_sqrt_sum_norm_sq
    {R : Register} {Branch : Type*}
    (indices : Finset Branch) (source : Branch → R.Index)
    (sourceInjective : Function.Injective source)
    (amplitude : Branch → ℂ) :
    ‖∑ branch ∈ indices,
        amplitude branch •
          (NormalizedVector.ket (source branch) : HilbertVector R)‖ =
      Real.sqrt (∑ branch ∈ indices, ‖amplitude branch‖ ^ 2) := by
  classical
  let basisKet : Branch → HilbertVector R := fun branch =>
    (NormalizedVector.ket (source branch) : HilbertVector R)
  have orthonormalBasisKet : Orthonormal ℂ basisKet := by
    change Orthonormal ℂ
      (fun branch => PiLp.single (β := fun _ : R.Index => ℂ)
        2 (source branch) (1 : ℂ))
    have orthonormalSingles :=
      (EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := R.Index)).comp
        source sourceInjective
    change Orthonormal ℂ
      (fun branch => PiLp.single (β := fun _ : R.Index => ℂ)
        2 (source branch) (1 : ℂ)) at orthonormalSingles
    exact orthonormalSingles
  have innerEquality := orthonormalBasisKet.inner_sum amplitude amplitude indices
  have normSquareEquality :
      ‖∑ branch ∈ indices,
          amplitude branch •
            (NormalizedVector.ket (source branch) : HilbertVector R)‖ ^ 2 =
        ∑ branch ∈ indices, ‖amplitude branch‖ ^ 2 := by
    change
      ‖∑ branch ∈ indices, amplitude branch • basisKet branch‖ ^ 2 = _
    rw [inner_self_eq_norm_sq_to_K] at innerEquality
    simp_rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq] at innerEquality
    apply Complex.ofReal_injective
    calc
      ((‖∑ branch ∈ indices,
          amplitude branch • basisKet branch‖ ^ 2 : ℝ) : ℂ) =
          ((‖∑ branch ∈ indices,
            amplitude branch • basisKet branch‖ : ℝ) : ℂ) ^ 2 :=
        Complex.ofReal_pow _ _
      _ = ∑ branch ∈ indices,
          ((‖amplitude branch‖ ^ 2 : ℝ) : ℂ) := innerEquality
      _ = ((∑ branch ∈ indices,
          ‖amplitude branch‖ ^ 2 : ℝ) : ℂ) := by
        exact (Complex.ofReal_sum indices
          (fun branch => ‖amplitude branch‖ ^ 2)).symm
  rw [← Real.sqrt_sq (norm_nonneg _), normSquareEquality]

end HilbertVector

namespace UnitaryOperator

/-- If two unitaries agree on every computational-basis label in `good`,
their outputs on an arbitrary state differ by at most twice the norm of the
state's component supported on the complementary `bad` labels. -/
theorem applyVec_sub_norm_le_two_mul_badPart_norm
    {R : Register} (actual ideal : UnitaryOperator R)
    (good bad : Finset R.Index)
    (partition : good ∪ bad = Finset.univ)
    (disjoint : Disjoint good bad)
    (agree : ∀ index ∈ good,
      actual.applyVec
          (NormalizedVector.ket index : HilbertVector R) =
        ideal.applyVec
          (NormalizedVector.ket index : HilbertVector R))
    (state : HilbertVector R) :
    ‖actual.applyVec state - ideal.applyVec state‖ ≤
      2 * ‖∑ index ∈ bad,
        state index • (NormalizedVector.ket index : HilbertVector R)‖ := by
  classical
  let goodPart : HilbertVector R :=
    ∑ index ∈ good,
      state index • (NormalizedVector.ket index : HilbertVector R)
  let badPart : HilbertVector R :=
    ∑ index ∈ bad,
      state index • (NormalizedVector.ket index : HilbertVector R)
  have state_split : state = goodPart + badPart := by
    symm
    calc
      goodPart + badPart =
          (∑ index ∈ good,
            state index •
              (NormalizedVector.ket index : HilbertVector R)) +
            ∑ index ∈ bad,
              state index •
                (NormalizedVector.ket index : HilbertVector R) := rfl
      _ = ∑ index ∈ good ∪ bad,
          state index •
            (NormalizedVector.ket index : HilbertVector R) :=
        (Finset.sum_union disjoint).symm
      _ = ∑ index : R.Index,
          state index •
            (NormalizedVector.ket index : HilbertVector R) := by
        rw [partition]
      _ = state := HilbertVector.sum_amplitude_smul_ket state
  have applyVec_finset_sum
      (operator : UnitaryOperator R) (indices : Finset R.Index)
      (term : R.Index → HilbertVector R) :
      operator.applyVec (∑ index ∈ indices, term index) =
        ∑ index ∈ indices, operator.applyVec (term index) := by
    induction indices using Finset.induction_on with
    | empty =>
        apply WithLp.ofLp_injective
        funext output
        simp [UnitaryOperator.applyVec_apply]
    | @insert index rest fresh ih =>
        rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
          applyVec_add, ih]
  have agree_goodPart :
      actual.applyVec goodPart = ideal.applyVec goodPart := by
    dsimp only [goodPart]
    rw [applyVec_finset_sum, applyVec_finset_sum]
    apply Finset.sum_congr rfl
    intro index member
    rw [applyVec_smul, applyVec_smul, agree index member]
  calc
    ‖actual.applyVec state - ideal.applyVec state‖ =
        ‖actual.applyVec badPart - ideal.applyVec badPart‖ := by
      rw [state_split, applyVec_add, applyVec_add, agree_goodPart]
      abel_nf
    _ ≤ ‖actual.applyVec badPart‖ + ‖ideal.applyVec badPart‖ :=
      norm_sub_le _ _
    _ = 2 * ‖badPart‖ := by
      rw [actual.norm_applyVec, ideal.norm_applyVec]
      ring
    _ = 2 * ‖∑ index ∈ bad,
        state index • (NormalizedVector.ket index : HilbertVector R)‖ := rfl

/-- Support-indexed form of the hybrid estimate.  The supplied branch family
need only expand the particular state under comparison; the two operators may
act arbitrarily on every basis label outside that family. -/
theorem applyVec_sub_norm_le_two_mul_badBranchPart_norm
    {R : Register} {Branch : Type*} [DecidableEq Branch]
    (actual ideal : UnitaryOperator R)
    (branches good bad : Finset Branch)
    (partition : good ∪ bad = branches)
    (disjoint : Disjoint good bad)
    (source : Branch → R.Index) (amplitude : Branch → ℂ)
    (agree : ∀ branch ∈ good,
      actual.applyVec
          (NormalizedVector.ket (source branch) : HilbertVector R) =
        ideal.applyVec
          (NormalizedVector.ket (source branch) : HilbertVector R))
    (state : HilbertVector R)
    (stateExpansion :
      (∑ branch ∈ branches,
        amplitude branch •
          (NormalizedVector.ket (source branch) : HilbertVector R)) = state) :
    ‖actual.applyVec state - ideal.applyVec state‖ ≤
      2 * ‖∑ branch ∈ bad,
        amplitude branch •
          (NormalizedVector.ket (source branch) : HilbertVector R)‖ := by
  let goodPart : HilbertVector R :=
    ∑ branch ∈ good,
      amplitude branch •
        (NormalizedVector.ket (source branch) : HilbertVector R)
  let badPart : HilbertVector R :=
    ∑ branch ∈ bad,
      amplitude branch •
        (NormalizedVector.ket (source branch) : HilbertVector R)
  have stateSplit : state = goodPart + badPart := by
    rw [← stateExpansion]
    symm
    calc
      goodPart + badPart =
          (∑ branch ∈ good,
            amplitude branch •
              (NormalizedVector.ket (source branch) : HilbertVector R)) +
            ∑ branch ∈ bad,
              amplitude branch •
                (NormalizedVector.ket (source branch) : HilbertVector R) := rfl
      _ = ∑ branch ∈ good ∪ bad,
          amplitude branch •
            (NormalizedVector.ket (source branch) : HilbertVector R) :=
        (Finset.sum_union disjoint).symm
      _ = ∑ branch ∈ branches,
          amplitude branch •
            (NormalizedVector.ket (source branch) : HilbertVector R) := by
        rw [partition]
  have applyVecFinsetSum
      (operator : UnitaryOperator R) (indices : Finset Branch)
      (term : Branch → HilbertVector R) :
      operator.applyVec (∑ branch ∈ indices, term branch) =
        ∑ branch ∈ indices, operator.applyVec (term branch) := by
    induction indices using Finset.induction_on with
    | empty =>
        apply WithLp.ofLp_injective
        funext output
        simp [UnitaryOperator.applyVec_apply]
    | @insert branch rest fresh induction =>
        rw [Finset.sum_insert fresh, Finset.sum_insert fresh,
          applyVec_add, induction]
  have agreeGoodPart :
      actual.applyVec goodPart = ideal.applyVec goodPart := by
    dsimp only [goodPart]
    rw [applyVecFinsetSum, applyVecFinsetSum]
    apply Finset.sum_congr rfl
    intro branch member
    rw [applyVec_smul, applyVec_smul, agree branch member]
  calc
    ‖actual.applyVec state - ideal.applyVec state‖ =
        ‖actual.applyVec badPart - ideal.applyVec badPart‖ := by
      rw [stateSplit, applyVec_add, applyVec_add, agreeGoodPart]
      abel_nf
    _ ≤ ‖actual.applyVec badPart‖ + ‖ideal.applyVec badPart‖ :=
      norm_sub_le _ _
    _ = 2 * ‖badPart‖ := by
      rw [actual.norm_applyVec, ideal.norm_applyVec]
      ring
    _ = 2 * ‖∑ branch ∈ bad,
        amplitude branch •
          (NormalizedVector.ket (source branch) : HilbertVector R)‖ := rfl

end UnitaryOperator

end

end QuantumAlg

end
