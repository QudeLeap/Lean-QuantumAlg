/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.Walk.Construction
import all QuantumAlg.Analysis.Walk.Construction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Ideal amplification in the edge-state plane

The exact reflection pair has the usual closed form and squared marked amplitude
[dW19, qcnotes.tex:2914-2961]. These are operator identities without an execution claim.
-/

section

namespace QuantumAlg.QuantumWalk

open NormalizedVector
open scoped BigOperators ComplexConjugate

noncomputable section

variable {n : ℕ}

/-! ### Search angle and marked fraction -/

/-- Fraction of vertices that are marked: `|M| / N`. -/
public def markedFraction {n : ℕ} (M : Finset (Fin (2 ^ n))) : ℝ :=
  (M.card : ℝ) / ((2 : ℝ) ^ n)

/-- Search angle `θ = arcsin(√ε)` for the quantum walk. -/
public def searchAngle {n : ℕ} (M : Finset (Fin (2 ^ n))) : ℝ :=
  Real.arcsin (Real.sqrt (markedFraction M))

/-! ### Geometric properties -/

section AAProperties
variable (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (M : Finset (Fin (2 ^ n)))

theorem outerProductOp_applyVec (ψ φ : HilbertVector (Qubits (n + n))) :
    HilbertOperator.applyVec (outerProductOp ψ) φ = inner ℂ ψ φ • ψ := by
  ext i
  simp [HilbertOperator.applyVec_apply, outerProductOp, Matrix.of_apply, PiLp.inner_apply,
    Finset.mul_sum, mul_comm, mul_left_comm, smul_eq_mul]
theorem markedProjectorOp_applyVec_edgeBasis_single (x y : Fin (2 ^ n)) :
    HilbertOperator.applyVec
      (HilbertOperator.tensor (OrthogonalProjector.basisOp x) (1 : HilbertOperator (Qubits n)))
      ((edgeBasis P y : HilbertVector (Qubits (n + n))))
    = if x = y then (edgeBasis P y : HilbertVector (Qubits (n + n))) else 0 := by
  rw [edgeBasis_coe, HilbertOperator.tensor_applyVec_tensor]
  have h_proj : HilbertOperator.applyVec (OrthogonalProjector.basisOp x) ((NormalizedVector.ket
  y).1)
      = if x = y then (NormalizedVector.ket y).1 else 0 := by
    by_cases hxy : x = y
    · subst hxy
      ext i; dsimp [OrthogonalProjector.basisOp]; simp [NormalizedVector.ket_apply, Finset.mem_univ]
    · ext i
      dsimp [OrthogonalProjector.basisOp]
      simp [ NormalizedVector.ket_apply, Finset.mem_univ, hxy, Ne.symm hxy]
  by_cases hxy : x = y
  · subst y; simp [h_proj, HilbertOperator.one_applyVec]
  · simp [h_proj, HilbertOperator.one_applyVec, hxy]

theorem markedProjectorOp_applyVec_edgeBasis (x : Fin (2 ^ n)) :
    HilbertOperator.applyVec (markedProjectorOp M) ((edgeBasis P x : HilbertVector (Qubits (n +
      n)))) =
      if x ∈ M then (edgeBasis P x : HilbertVector (Qubits (n + n))) else 0 := by
  rw [markedProjectorOp]
  induction M using Finset.induction with
  | empty => ext i; simp [HilbertOperator.applyVec_apply, edgeBasis]
  | insert y M hy ih =>
      rw [Finset.sum_insert hy]
      have h_add : HilbertOperator.applyVec
          (HilbertOperator.tensor (OrthogonalProjector.basisOp y) (1 : HilbertOperator (Qubits n))
            + ∑ z ∈ M, HilbertOperator.tensor (OrthogonalProjector.basisOp z) (1 : HilbertOperator
            (Qubits n)))
          ((edgeBasis P x : HilbertVector (Qubits (n + n))))
          = HilbertOperator.applyVec (HilbertOperator.tensor (OrthogonalProjector.basisOp y)
              (1 : HilbertOperator (Qubits n))) ((edgeBasis P x : HilbertVector (Qubits (n + n))))
            + HilbertOperator.applyVec (∑ z ∈ M, HilbertOperator.tensor
            (OrthogonalProjector.basisOp z)
                (1 : HilbertOperator (Qubits n))) ((edgeBasis P x : HilbertVector (Qubits (n +
                  n)))) := by
        simp
      rw [h_add, ih, markedProjectorOp_applyVec_edgeBasis_single P y x]
      by_cases hyx : x = y
      · subst hyx; simp [hy]
      · have hyx' := Ne.symm hyx
        by_cases hxM : x ∈ M
        · have hinsert : x ∈ insert y M := Finset.mem_insert_of_mem hxM
          simp [hyx', hxM, hinsert]
        · have hinsert : x ∉ insert y M := by simp [hyx, hxM]
          simp [hyx', hxM, hinsert]

theorem markedProjectorOp_applyVec_edgeBasis'
    (P : Matrix.SymmetricStochastic (Fin (2 ^ n))) (x : Fin (2 ^ n)) (hx : x ∉ M) :
    HilbertOperator.applyVec (markedProjectorOp M) ((edgeBasis P x : HilbertVector (Qubits (n +
      n)))) = 0 := by
  rw [markedProjectorOp_applyVec_edgeBasis P M x, if_neg hx]

private lemma applyVec_zero (A : HilbertOperator (Qubits (n + n))) :
    HilbertOperator.applyVec A 0 = 0 := by
  ext i; simp [HilbertOperator.applyVec_apply]

private lemma map_sum_edgeBasis (A : HilbertOperator (Qubits (n + n))) (s : Finset (Fin (2 ^ n))) :
    HilbertOperator.applyVec A (∑ x ∈ s, (edgeBasis P x : HilbertVector (Qubits (n + n)))) =
    ∑ x ∈ s, HilbertOperator.applyVec A ((edgeBasis P x : HilbertVector (Qubits (n + n)))) := by
  induction s using Finset.induction with
  | empty => simp [applyVec_zero]
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, HilbertOperator.applyVec_add, ih, Finset.sum_insert hx]

theorem refBglobalOp_applyVec_badState (_hM_proper : M ≠ Finset.univ) :
    HilbertOperator.applyVec ((refBglobalOp M : HilbertOperator (Qubits (n + n)))) (badState P
      M) = badState P M := by
  rw [refBglobalOp_coe, HilbertOperator.sub_applyVec, HilbertOperator.one_applyVec,
    HilbertOperator.smul_applyVec]
  have hzero : HilbertOperator.applyVec (markedProjectorOp M) (badState P M) = 0 := by
    rw [badState, HilbertOperator.applyVec_smul, map_sum_edgeBasis]
    have hsum : (∑ x ∈ (Finset.univ : Finset (Fin (2 ^ n))) \ M,
        HilbertOperator.applyVec (markedProjectorOp M) ((edgeBasis P x : HilbertVector (Qubits (n
          + n))))) = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      rw [Finset.mem_sdiff] at hx
      exact markedProjectorOp_applyVec_edgeBasis' (P := P) (M := M) x hx.2
    rw [hsum, smul_zero]
  rw [hzero]; simp

theorem refBglobalOp_applyVec_goodState (_hM_nonempty : M.Nonempty) :
    HilbertOperator.applyVec ((refBglobalOp M : HilbertOperator (Qubits (n + n)))) (goodState P
      M) = -(goodState P M) := by
  rw [refBglobalOp_coe, HilbertOperator.sub_applyVec, HilbertOperator.one_applyVec,
    HilbertOperator.smul_applyVec]
  have hone : HilbertOperator.applyVec (markedProjectorOp M) (goodState P M) = goodState P M := by
    rw [goodState, HilbertOperator.applyVec_smul, map_sum_edgeBasis]
    have hinner : (∑ x ∈ M, HilbertOperator.applyVec (markedProjectorOp M) ((edgeBasis P x :
      HilbertVector (Qubits (n + n)))))
               = (∑ x ∈ M, (edgeBasis P x : HilbertVector (Qubits (n + n)))) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [markedProjectorOp_applyVec_edgeBasis P M x, if_pos hx]
    rw [hinner]
  rw [hone]
  calc
    goodState P M - (2 : ℂ) • goodState P M
        = ((1 : ℂ) - (2 : ℂ)) • goodState P M := by rw [sub_smul, one_smul]
    _ = (-1 : ℂ) • goodState P M := by ring_nf
    _ = -goodState P M := by simp

public theorem uniformEdgeState_inner_goodState_eq_sin (hM_nonempty : M.Nonempty) :
    inner ℂ ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (goodState P M) = Real.sin
      (searchAngle M) := by
  have hε : markedFraction M ≤ 1 := by
    rw [markedFraction]
    exact (div_le_one (by positivity)).mpr
      (by exact_mod_cast (Finset.card_le_univ M).trans_eq (by simp))
  have h_nonneg : 0 ≤ Real.sqrt (markedFraction M) := Real.sqrt_nonneg _
  have h_le_one : Real.sqrt (markedFraction M) ≤ 1 := by
    exact Real.sqrt_le_one.mpr hε
  rw [searchAngle, Real.sin_arcsin (by linarith) h_le_one, markedFraction]
  exact uniformEdgeState_inner_goodState P M hM_nonempty

public theorem uniformEdgeState_inner_badState_eq_cos (hM_proper : M ≠ Finset.univ) :
    inner ℂ ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (badState P M) = Real.cos
      (searchAngle M) := by
  rw [uniformEdgeState_inner_badState P M hM_proper]
  rw [searchAngle, Real.cos_arcsin (Real.sqrt (markedFraction M))]
  have hpos : 0 ≤ markedFraction M := by
    rw [markedFraction]
    refine div_nonneg (by exact_mod_cast Nat.zero_le _) (by positivity)
  rw [Real.sq_sqrt hpos, markedFraction]
  congr 1
  field_simp

public theorem uniformEdgeState_decompose (hM_nonempty : M.Nonempty) (hM_proper : M ≠ Finset.univ) :
    ((uniformEdgeState P : HilbertVector (Qubits (n + n))) : HilbertVector (Qubits (n + n))) =
      (Real.sin (searchAngle M) : ℂ) • (goodState P M : HilbertVector (Qubits (n + n))) +
      (Real.cos (searchAngle M) : ℂ) • (badState P M : HilbertVector (Qubits (n + n))) := by
  ext i
  simp only [uniformEdgeState_coe, goodState, badState, PiLp.smul_apply, PiLp.add_apply,
    smul_eq_mul]
  have hNpos : ((2 : ℝ) ^ n : ℂ) ≠ 0 := by norm_num
  have hMpos : (M.card : ℂ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hM_nonempty
  have hNsubMpos : (((2 : ℝ) ^ n : ℝ) - M.card : ℂ) ≠ 0 := by
    intro hzero
    have hzero_re : ((2 : ℝ) ^ n : ℝ) - (M.card : ℝ) = (0 : ℝ) := by exact_mod_cast hzero
    have h_lt : M.card < 2 ^ n := by
      have h_ss : M ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hM_proper
      simpa using Finset.card_lt_card h_ss
    have h_lt' : (M.card : ℝ) < ((2 : ℝ) ^ n) := by exact_mod_cast h_lt
    linarith
  -- Prove the normalization identities over the reals, then cast them to complex scalars.
  have h_sin_real : Real.sin (searchAngle M) * (Real.sqrt (M.card : ℝ))⁻¹ = (Real.sqrt ((2 : ℝ) ^
  n))⁻¹ := by
    rw [searchAngle]
    have h_frac_nonneg : 0 ≤ markedFraction M := by
      rw [markedFraction]; positivity
    have h_frac_le_one : markedFraction M ≤ 1 := by
      rw [markedFraction]; refine (div_le_one ?_).mpr ?_
      · positivity
      · exact_mod_cast (Finset.card_le_univ M).trans_eq (by simp)
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (markedFraction M) := Real.sqrt_nonneg _
    have h_sqrt_le_one : Real.sqrt (markedFraction M) ≤ 1 := Real.sqrt_le_one.mpr h_frac_le_one
    rw [Real.sin_arcsin (by linarith) h_sqrt_le_one]
    rw [markedFraction]
    rw [Real.sqrt_div (by positivity)]
    have h_sqrt_M_ne_zero : Real.sqrt (M.card : ℝ) ≠ 0 := by
      have hM_pos : 0 < (M.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hM_nonempty
      exact ne_of_gt (Real.sqrt_pos.mpr hM_pos)
    rw [div_eq_mul_inv]
    field_simp [h_sqrt_M_ne_zero]
  have h_cos_real : Real.cos (searchAngle M) * (Real.sqrt ((2 : ℝ) ^ n - M.card : ℝ))⁻¹ =
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ := by
    rw [searchAngle]
    have h_frac_nonneg : 0 ≤ markedFraction M := by
      rw [markedFraction]; positivity
    have h_frac_le_one : markedFraction M ≤ 1 := by
      rw [markedFraction]; refine (div_le_one ?_).mpr ?_
      · positivity
      · exact_mod_cast (Finset.card_le_univ M).trans_eq (by simp)
    rw [Real.cos_arcsin (Real.sqrt (markedFraction M))]
    rw [Real.sq_sqrt h_frac_nonneg]
    rw [markedFraction]
    have h_sub_eq : 1 - (M.card : ℝ) / (2 : ℝ) ^ n = ((2 : ℝ) ^ n - M.card) / (2 : ℝ) ^ n := by
      have h_div : (1 : ℝ) = (2 : ℝ) ^ n / (2 : ℝ) ^ n := by
        have : (2 : ℝ) ^ n ≠ 0 := by positivity
        exact (div_self this).symm
      rw [h_div, ← sub_div]
    rw [h_sub_eq]
    have h_ss : M ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hM_proper
    have h_card := Finset.card_lt_card h_ss
    have h_card_nat : M.card < 2 ^ n := by
      simpa using Finset.card_lt_card h_ss
    have h_lt' : (M.card : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast h_card_nat
    have h_sub_pos : 0 < (2 : ℝ) ^ n - (M.card : ℝ) := by linarith
    rw [Real.sqrt_div h_sub_pos.le]
    have h_sqrt_sub_ne_zero : Real.sqrt ((2 : ℝ) ^ n - M.card : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr h_sub_pos)
    rw [div_eq_mul_inv]
    field_simp [h_sqrt_sub_ne_zero]
  have h_sin_sqrt : (Real.sin (searchAngle M) : ℂ) * (Real.sqrt (M.card : ℝ) : ℂ)⁻¹ = (Real.sqrt
  ((2 : ℝ) ^ n) : ℂ)⁻¹ := by
    simpa [Complex.ofReal_sin] using congrArg (fun x : ℝ => (x : ℂ)) h_sin_real
  have h_cos_sqrt : (Real.cos (searchAngle M) : ℂ) * (Real.sqrt (((2 : ℝ) ^ n - M.card : ℝ)) : ℂ)⁻¹
  = (Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹ := by
    simpa [Complex.ofReal_cos] using congrArg (fun x : ℝ => (x : ℂ)) h_cos_real
  -- Push .ofLp i inside all sums
  have h_distrib (s : Finset (Fin (2 ^ n))) (f : Fin (2 ^ n) → HilbertVector (Qubits (n + n))) :
      (∑ x ∈ s, f x).ofLp i = ∑ x ∈ s, (f x).ofLp i := by
    simp
  simp only [h_distrib]
  calc
    ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * (∑ x : Fin (2 ^ n), ((edgeBasis P x : HilbertVector
      (Qubits (n + n)))).ofLp i)
        = ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * ((∑ x ∈ M, ((edgeBasis P x : HilbertVector (Qubits
          (n + n)))).ofLp i)
            + (∑ x ∈ (Finset.univ \ M), ((edgeBasis P x : HilbertVector (Qubits (n + n)))).ofLp
              i)) := by
      congr 1
      exact (Finset.sum_add_sum_compl M (fun x =>
        (edgeBasis P x : HilbertVector (Qubits (n + n))).ofLp i)).symm
    _ = ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * (∑ x ∈ M, ((edgeBasis P x : HilbertVector (Qubits (n +
      n)))).ofLp i)
          + ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * (∑ x ∈ (Finset.univ \ M), ((edgeBasis P x :
            HilbertVector (Qubits (n + n)))).ofLp i)
          := by ring
    _ = ((Real.sin (searchAngle M) : ℂ) * ((Real.sqrt (M.card : ℝ) : ℂ)⁻¹)) * (∑ x ∈ M, (edgeBasis
      P x : HilbertVector (Qubits (n + n))).ofLp i)
          + ((Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹) * (∑ x ∈ (Finset.univ \ M), ((edgeBasis P x :
            HilbertVector (Qubits (n + n)))).ofLp i)
          := by
      rw [← h_sin_sqrt]
    _ = ((Real.sin (searchAngle M) : ℂ) * ((Real.sqrt (M.card : ℝ) : ℂ)⁻¹)) * (∑ x ∈ M, (edgeBasis
      P x : HilbertVector (Qubits (n + n))).ofLp i)
          + ((Real.cos (searchAngle M) : ℂ) * ((Real.sqrt (((2 : ℝ) ^ n - M.card : ℝ)) : ℂ)⁻¹)) *
          (∑ x ∈ (Finset.univ \ M), ((edgeBasis P x : HilbertVector (Qubits (n + n)))).ofLp i) := by
      rw [← h_cos_sqrt]
    _ = ((Real.sin (searchAngle M) : ℂ) * ((Real.sqrt (M.card : ℝ) : ℂ)⁻¹ * (∑ x ∈ M, (edgeBasis P
      x : HilbertVector (Qubits (n + n))).ofLp i)))
          + ((Real.cos (searchAngle M) : ℂ) * ((Real.sqrt (((2 : ℝ) ^ n - M.card : ℝ)) : ℂ)⁻¹ * (∑
          x ∈ (Finset.univ \ M), ((edgeBasis P x : HilbertVector (Qubits (n + n)))).ofLp i))) :=
            by ring

theorem idealAA_iterate_applyVec_on_B (hM_nonempty : M.Nonempty) (hM_proper : M ≠ Finset.univ) :
    HilbertOperator.applyVec ((idealRefUOp P : HilbertOperator (Qubits (n + n))) * (refBglobalOp M
      : HilbertOperator (Qubits (n + n)))) (badState P M)
      = (Real.cos (2 * searchAngle M) : ℂ) • (badState P M : HilbertVector (Qubits (n + n))) +
        (Real.sin (2 * searchAngle M) : ℂ) • (goodState P M : HilbertVector (Qubits (n + n))) := by
  rw [HilbertOperator.mul_applyVec, refBglobalOp_applyVec_badState P M hM_proper]
  rw [idealRefUOp_coe, HilbertOperator.sub_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.one_applyVec]
  rw [outerProductOp_applyVec ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (badState P
    M)]
  rw [uniformEdgeState_inner_badState_eq_cos P M hM_proper]
  rw [uniformEdgeState_decompose P M hM_nonempty hM_proper]
  have hsin2 : (Real.sin (2 * searchAngle M) : ℂ) = 2 * (Real.cos (searchAngle M) : ℂ) * (Real.sin
  (searchAngle M) : ℂ) := by
    simp [Real.sin_two_mul, mul_comm, mul_left_comm]
  have hcos2 : (Real.cos (2 * searchAngle M) : ℂ) = 2 * (Real.cos (searchAngle M) : ℂ) ^ 2 - 1 := by
    simp [Real.cos_two_mul]
  simp [smul_add, smul_smul, mul_comm, mul_left_comm, hsin2, hcos2, sub_eq_add_neg, add_smul, sq,
  add_comm, add_left_comm, add_assoc]

theorem idealAA_iterate_applyVec_on_G (hM_nonempty : M.Nonempty) (hM_proper : M ≠ Finset.univ) :
    HilbertOperator.applyVec ((idealRefUOp P : HilbertOperator (Qubits (n + n))) * (refBglobalOp M
      : HilbertOperator (Qubits (n + n)))) (goodState P M)
      = (Real.cos (2 * searchAngle M) : ℂ) • (goodState P M : HilbertVector (Qubits (n + n))) -
        (Real.sin (2 * searchAngle M) : ℂ) • (badState P M : HilbertVector (Qubits (n + n))) := by
  rw [HilbertOperator.mul_applyVec, refBglobalOp_applyVec_goodState P M hM_nonempty]
  simp only [HilbertOperator.applyVec_neg]
  rw [idealRefUOp_coe, HilbertOperator.sub_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.one_applyVec]
  rw [outerProductOp_applyVec ((uniformEdgeState P : HilbertVector (Qubits (n + n)))) (goodState P
    M)]
  rw [uniformEdgeState_inner_goodState_eq_sin P M hM_nonempty]
  rw [uniformEdgeState_decompose P M hM_nonempty hM_proper]
  have hsin2 : (Real.sin (2 * searchAngle M) : ℂ) = 2 * (Real.cos (searchAngle M) : ℂ) * (Real.sin
  (searchAngle M) : ℂ) := by
    simp [Real.sin_two_mul, mul_comm, mul_left_comm]
  have hcos2' : (Real.cos (2 * searchAngle M) : ℂ) = 1 - 2 * (Real.sin (searchAngle M) : ℂ) ^ 2 :=
  by
    have h : Real.cos (2 * searchAngle M) = 1 - 2 * Real.sin (searchAngle M) ^ 2 := by
      rw [Real.cos_two_mul]
      nlinarith [Real.cos_sq_add_sin_sq (searchAngle M)]
    exact_mod_cast h
  simp [smul_add, smul_smul, mul_comm, mul_left_comm, hsin2, hcos2', sq, sub_eq_add_neg, add_smul,
  add_comm, add_left_comm, add_assoc]

public theorem idealAA_k_iterates (hM_nonempty : M.Nonempty) (hM_proper : M ≠ Finset.univ) (k : ℕ) :
    ((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P)
      = (Real.cos (((2 * (k : ℝ) + 1) * searchAngle M)) : ℂ) •
          (badState P M : HilbertVector (Qubits (n + n))) +
        (Real.sin (((2 * (k : ℝ) + 1) * searchAngle M)) : ℂ) •
          (goodState P M : HilbertVector (Qubits (n + n))) := by
  change HilbertOperator.applyVec (((idealRefUOp P : HilbertOperator (Qubits (n + n))) *
    (refBglobalOp M : HilbertOperator (Qubits (n + n)))) ^ k) ((uniformEdgeState P : HilbertVector
      (Qubits
      (n + n))))
      = (Real.cos (((2 * (k : ℝ) + 1) * searchAngle M)) : ℂ) •
          (badState P M : HilbertVector (Qubits (n + n))) +
        (Real.sin (((2 * (k : ℝ) + 1) * searchAngle M)) : ℂ) •
          (goodState P M : HilbertVector (Qubits (n + n)))
  induction k with
  | zero =>
      simpa only [pow_zero, HilbertOperator.one_applyVec, Nat.cast_zero, mul_zero,
        zero_add, one_mul, add_comm] using
        uniformEdgeState_decompose P M hM_nonempty hM_proper
  | succ k ih =>
      rw [pow_succ', HilbertOperator.mul_applyVec, ih]
      rw [HilbertOperator.applyVec_add, HilbertOperator.applyVec_smul,
        HilbertOperator.applyVec_smul]
      rw [idealAA_iterate_applyVec_on_B P M hM_nonempty hM_proper,
        idealAA_iterate_applyVec_on_G P M hM_nonempty hM_proper]
      have h_angle : ((2 * (k : ℝ) + 1) * searchAngle M) + 2 * searchAngle M
            = ((2 * ((k + 1 : ℕ) : ℝ) + 1) * searchAngle M) := by
        push_cast; ring
      rw [← h_angle, Real.cos_add, Real.sin_add]
      push_cast
      module

public theorem idealAA_success_probability (hM_nonempty : M.Nonempty) (hM_proper : M ≠
  Finset.univ) (k :
ℕ) :
    let finalState := ((idealRefUOp P * refBglobalOp M) ^ k).applyVec (uniformEdgeState P)
    Complex.normSq (inner ℂ (goodState P M) finalState) =
      (Real.sin (((2 * (k : ℝ) + 1) * searchAngle M))) ^ 2 := by
  intro finalState
  dsimp [finalState] at *
  rw [idealAA_k_iterates P M hM_nonempty hM_proper k]
  have h_self : inner ℂ (goodState P M) (goodState P M) = 1 := by
    have hnorm := goodState_norm P M hM_nonempty
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (goodState P M)
    rw [h, hnorm]; norm_num
  simp [inner_add_right, inner_smul_right, goodState_inner_badState_eq_zero P M,
    goodState_norm P M hM_nonempty]
  simpa [Complex.ofReal_sin, sq] using
    Complex.normSq_ofReal (Real.sin (((2 * (k : ℝ) + 1) * searchAngle M)))

end AAProperties
end
end QuantumAlg.QuantumWalk

end
