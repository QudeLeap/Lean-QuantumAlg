/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Simulation.GSimLocal
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Polynomial-size DLA dichotomy schema

This module isolates the polynomial side of the Lie-algebraic dichotomy. An
inverse-polynomial variance floor rules out exponential concentration, while
membership of the observable in a polynomial-dimensional dynamical Lie algebra
keeps the exact g-sim reconstruction data polynomial in the register size.
-/

@[expose] public section

namespace QuantumAlg

open Filter Matrix Topology

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem tendsto_succ_pow_div_const_pow (k : ℕ) {b : ℝ} (hb : 1 < b) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ k) / b ^ n) atTop (𝓝 0) := by
  have hsucc :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ k) / b ^ (n + 1)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt k hb).comp (tendsto_add_atTop_nat 1)
  have hb0 : b ≠ 0 := ne_of_gt (one_pos.trans hb)
  have hmul :
      Tendsto (fun n : ℕ => b * ((((n : ℝ) + 1) ^ k) / b ^ (n + 1))) atTop
        (𝓝 0) := by
    simpa using hsucc.const_mul b
  refine hmul.congr' ?_
  filter_upwards with n
  field_simp [pow_succ, hb0]
  ring

/-- An inverse-polynomial lower bound on a variance sequence rules out a barren plateau. -/
theorem not_hasBarrenPlateau_of_invPoly_lower (v : ℕ → ℝ)
    {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hlower : ∀ n : ℕ, c / (((n : ℝ) + 1) ^ k) ≤ v n) :
    ¬ HasBarrenPlateau v := by
  intro hbp
  obtain ⟨b, hb, C, _hC, hupper⟩ := hbp
  have htendsto :
      Tendsto (fun n : ℕ => (C / c) * ((((n : ℝ) + 1) ^ k) / b ^ n)) atTop
        (𝓝 0) := by
    simpa using (tendsto_succ_pow_div_const_pow k hb).const_mul (C / c)
  obtain ⟨N, hsmall⟩ := (htendsto.eventually (gt_mem_nhds zero_lt_one)).exists
  have hpoly_pos : 0 < (((N : ℝ) + 1) ^ k) := pow_pos (by positivity) k
  have hbpow_pos : 0 < b ^ N := pow_pos (one_pos.trans hb) N
  have hlow_abs : c / (((N : ℝ) + 1) ^ k) ≤ |v N - 0| := by
    rw [sub_zero]
    exact le_trans (hlower N) (le_abs_self (v N))
  have hineq : c / (((N : ℝ) + 1) ^ k) ≤ C / b ^ N :=
    le_trans hlow_abs (hupper N)
  have hone_le : 1 ≤ (C / c) * ((((N : ℝ) + 1) ^ k) / b ^ N) := by
    field_simp [hc.ne', hpoly_pos.ne', hbpow_pos.ne'] at hineq ⊢
    nlinarith [hineq, hc, hpoly_pos, hbpow_pos]
  exact (not_lt_of_ge hone_le) hsmall

private theorem reductive_variance_floor_of_distinguished_purity
    {N : ℕ} {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (R : RagoneReductive ρ O) (hρ : ρᴴ = ρ) (hO : Oᴴ = O)
    (hdim : ∀ j, 0 < (R.basis j).dim) (j0 : Fin R.numComp)
    {Cp cq : ℝ} (hCp : 0 < Cp) (hcq : 0 < cq) {kp kq n : ℕ}
    (hdim_j0 : (((R.basis j0).dim : ℝ) ≤ Cp * (((n : ℝ) + 1) ^ kp)))
    (hfloor :
      cq / (((n : ℝ) + 1) ^ kq)
        ≤ ‖(R.basis j0).gPurity ρ * (R.basis j0).gPurity O‖) :
    (cq / Cp) / (((n : ℝ) + 1) ^ (kq + kp)) ≤ R.variance := by
  let term : Fin R.numComp → ℂ := fun j =>
    (R.basis j).gPurity ρ * (R.basis j).gPurity O / ((R.basis j).dim : ℂ)
  have hvarC : (R.variance : ℂ) = ∑ j, term j := by
    simpa [term] using R.totalVariance_eq hρ hO hdim
  have hvar_re : R.variance = (∑ j, term j).re := by
    calc
      R.variance = ((R.variance : ℂ).re) := by simp
      _ = (∑ j, term j).re := by rw [hvarC]
  have hterm_nonneg : ∀ j, 0 ≤ (term j).re := by
    intro j
    obtain ⟨r, hr, hprod⟩ := (R.basis j).gPurity_mul_gPurity_nonneg_real ρ O
    have hdimR : 0 ≤ (((R.basis j).dim : ℝ)) := by positivity
    have hterm_eq : (term j).re = r / ((R.basis j).dim : ℝ) := by
      dsimp [term]
      rw [hprod]
      change (((r : ℂ) / (((R.basis j).dim : ℝ) : ℂ)).re
        = r / ((R.basis j).dim : ℝ))
      simp
    rw [hterm_eq]
    exact div_nonneg hr hdimR
  have hj0_le_sum : (term j0).re ≤ (∑ j, term j).re := by
    calc
      (term j0).re ≤ ∑ j, (term j).re :=
        Finset.single_le_sum (fun j _ => hterm_nonneg j) (Finset.mem_univ j0)
      _ = (∑ j, term j).re := by simp
  have hterm_floor :
      (cq / Cp) / (((n : ℝ) + 1) ^ (kq + kp)) ≤ (term j0).re := by
    obtain ⟨r0, hr0, hprod0⟩ :=
      (R.basis j0).gPurity_mul_gPurity_nonneg_real ρ O
    have hx_pos : 0 < (n : ℝ) + 1 := by positivity
    have hx_ne : (n : ℝ) + 1 ≠ 0 := ne_of_gt hx_pos
    have hxkq_pos : 0 < (((n : ℝ) + 1) ^ kq) := pow_pos hx_pos kq
    have hdim0_pos : 0 < (((R.basis j0).dim : ℝ)) := by exact_mod_cast hdim j0
    have hnum_nonneg : 0 ≤ cq / (((n : ℝ) + 1) ^ kq) :=
      div_nonneg hcq.le hxkq_pos.le
    have hterm0_eq : (term j0).re = r0 / ((R.basis j0).dim : ℝ) := by
      dsimp [term]
      rw [hprod0]
      change (((r0 : ℂ) / (((R.basis j0).dim : ℝ) : ℂ)).re
        = r0 / ((R.basis j0).dim : ℝ))
      simp
    have hnorm_eq :
        ‖(R.basis j0).gPurity ρ * (R.basis j0).gPurity O‖ = r0 := by
      rw [hprod0]
      exact (RCLike.norm_ofReal (K := ℂ) r0).trans (abs_of_nonneg hr0)
    have hfloor_r : cq / (((n : ℝ) + 1) ^ kq) ≤ r0 := by
      rw [← hnorm_eq]
      exact hfloor
    have hden_step :
        (cq / (((n : ℝ) + 1) ^ kq)) / (Cp * (((n : ℝ) + 1) ^ kp))
          ≤ (cq / (((n : ℝ) + 1) ^ kq)) / ((R.basis j0).dim : ℝ) :=
      div_le_div_of_nonneg_left hnum_nonneg hdim0_pos hdim_j0
    have hnum_step :
        (cq / (((n : ℝ) + 1) ^ kq)) / ((R.basis j0).dim : ℝ)
          ≤ r0 / ((R.basis j0).dim : ℝ) :=
      div_le_div_of_nonneg_right hfloor_r hdim0_pos.le
    have harith :
        (cq / Cp) / (((n : ℝ) + 1) ^ (kq + kp))
          = (cq / (((n : ℝ) + 1) ^ kq)) / (Cp * (((n : ℝ) + 1) ^ kp)) := by
      rw [pow_add]
      field_simp [hCp.ne', hx_ne]
    calc
      (cq / Cp) / (((n : ℝ) + 1) ^ (kq + kp))
          = (cq / (((n : ℝ) + 1) ^ kq)) / (Cp * (((n : ℝ) + 1) ^ kp)) := harith
      _ ≤ (cq / (((n : ℝ) + 1) ^ kq)) / ((R.basis j0).dim : ℝ) := hden_step
      _ ≤ r0 / ((R.basis j0).dim : ℝ) := hnum_step
      _ = (term j0).re := hterm0_eq.symm
  exact hterm_floor.trans (hj0_le_sum.trans_eq hvar_re.symm)

/-- A polynomial-size reductive DLA family with an inverse-polynomial distinguished-ideal
purity floor has no barren plateau, and every loss with observable in the whole DLA is
exactly reconstructed from the `dim g` g-sim data. -/
theorem polyDLA_family_dichotomy
    {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    (b : (n : ℕ) → DLAHermBasis (gens n))
    (R : (n : ℕ) → RagoneReductive (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n)
    (hdim : ∀ n j, 0 < ((R n).basis j).dim)
    (hOmem : ∀ n, O n ∈ (dynamicalLieAlgebra (gens n)).toSubmodule)
    {CpData : ℝ} {kpData : ℕ}
    (_hwhole_dim : ∀ n, (((b n).dim : ℝ) ≤ CpData * (((n : ℝ) + 1) ^ kpData)))
    (j0 : (n : ℕ) → Fin (R n).numComp)
    {CpIdeal : ℝ} (hCpIdeal : 0 < CpIdeal) {kpIdeal : ℕ}
    (hdim_j0 : ∀ n,
      (((R n).basis (j0 n)).dim : ℝ) ≤ CpIdeal * (((n : ℝ) + 1) ^ kpIdeal))
    {cq : ℝ} (hcq : 0 < cq) {kq : ℕ}
    (hfloor : ∀ n : ℕ,
      cq / (((n : ℝ) + 1) ^ kq)
        ≤ ‖((R n).basis (j0 n)).gPurity (ρ n) * ((R n).basis (j0 n)).gPurity (O n)‖) :
    ¬ HasBarrenPlateau (fun n => (R n).variance)
      ∧ ∀ n (Gs : List (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)),
          (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (gens n)).toSubmodule) →
          ((Gs.map NormedSpace.exp).prod * ρ n
              * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O n).trace
            = ∑ j, hsInner ((b n).B j) (gsimEvolved Gs (O n))
                * (ρ n * (b n).B j).trace := by
  refine ⟨?_, ?_⟩
  · refine not_hasBarrenPlateau_of_invPoly_lower (fun n => (R n).variance)
      (div_pos hcq hCpIdeal) (kq + kpIdeal) ?_
    intro n
    exact reductive_variance_floor_of_distinguished_purity (R n) (hρ n) (hO n)
      (hdim n) (j0 n) hCpIdeal hcq (hdim_j0 n) (hfloor n)
  · intro n Gs hGs
    exact gsim_loss_reconstruction_ansatz (b n) hGs (ρ n) (hOmem n)

/-- Product-local `su(2)^n` has an inverse-polynomial reductive witness and exact
reconstruction from the `3n` local-DLA data, indexed by `m + 1` qubits. -/
theorem localObs_polyDLA_family_dichotomy :
    ¬ HasBarrenPlateau
        (fun m => (rLocalProductClifford (n := m + 1) (Nat.succ_pos m)).variance)
      ∧ (∀ m, (((localHermBasis (m + 1)).dim : ℝ) ≤ 3 * (((m : ℝ) + 1) ^ 1)))
      ∧ ∀ m (Gs : List (Matrix (Fin (2 ^ (m + 1))) (Fin (2 ^ (m + 1))) ℂ)),
          (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (localGens (m + 1))).toSubmodule) →
          ((Gs.map NormedSpace.exp).prod * localState
              * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod
              * localObs (Nat.succ_pos m)).trace
            = ∑ j, hsInner ((localHermBasis (m + 1)).B j)
                (gsimEvolved Gs (localObs (Nat.succ_pos m)))
                * (localState * (localHermBasis (m + 1)).B j).trace := by
  have hpoly :
      ¬ HasBarrenPlateau
          (fun m => (rLocalProductClifford (n := m + 1) (Nat.succ_pos m)).variance)
        ∧ ∀ m (Gs : List (Matrix (Fin (2 ^ (m + 1))) (Fin (2 ^ (m + 1))) ℂ)),
            (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (localGens (m + 1))).toSubmodule) →
            ((Gs.map NormedSpace.exp).prod * localState
                * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod
                * localObs (Nat.succ_pos m)).trace
              = ∑ j, hsInner ((localHermBasis (m + 1)).B j)
                  (gsimEvolved Gs (localObs (Nat.succ_pos m)))
                  * (localState * (localHermBasis (m + 1)).B j).trace := by
    refine polyDLA_family_dichotomy
      (sz := fun m => 2 ^ (m + 1))
      (gens := fun m => localGens (m + 1))
      (ρ := fun m => localState (n := m + 1))
      (O := fun m => localObs (Nat.succ_pos m))
      (b := fun m => localHermBasis (m + 1))
      (R := fun m => rLocalProductClifford (Nat.succ_pos m))
      (CpData := 3) (kpData := 1)
      (j0 := fun m => (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)))
      (CpIdeal := 3) (kpIdeal := 0) (cq := 1) (kq := 0)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro m
      exact localState_herm
    · intro m
      exact localObs_herm (Nat.succ_pos m)
    · intro m j
      exact su2EmbHermBasis_dim_pos j
    · intro m
      exact localObs_mem_product_dla (Nat.succ_pos m)
    · intro m
      rw [localHermBasis_dim]
      norm_num
    · norm_num
    · intro m
      dsimp [rLocalProductClifford]
      norm_num
    · norm_num
    · intro m
      change 1 / (((m : ℝ) + 1) ^ 0)
        ≤ ‖(su2EmbHermBasis (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))).gPurity
              (localState (n := m + 1))
            * (su2EmbHermBasis (⟨0, Nat.succ_pos m⟩ : Fin (m + 1))).gPurity
              (localObs (Nat.succ_pos m))‖
      rw [gPurity_localState, gPurity_localObs_diag]
      have hpow : (2 ^ (m + 1) : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [inv_mul_cancel₀ hpow]
      norm_num
  refine ⟨hpoly.1, ?_, hpoly.2⟩
  · intro m
    rw [localHermBasis_dim]
    norm_num

end QuantumAlg
