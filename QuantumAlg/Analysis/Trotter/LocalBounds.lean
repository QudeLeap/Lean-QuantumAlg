/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Analysis.Trotter.CommutatorProduct
public import QuantumAlg.Components.Pauli.FermiHubbard.Local.Interaction
public import QuantumAlg.Components.Pauli.FermiHubbard.Local.Kinetic
import all QuantumAlg.Components.Pauli.FermiHubbard.Local.Interaction
import all QuantumAlg.Components.Pauli.FermiHubbard.Local.Kinetic
import all QuantumAlg.Components.Pauli.JordanWigner.LocalAlgebra
import all QuantumAlg.Components.Pauli.JordanWigner.Permutations
import all QuantumAlg.Core.Base.Gate.OperatorNorm
import Mathlib.Tactic

/-!
# Local interaction contributions to the Hubbard commutator bound

The four-neighbor Majorana action and the second-order product rule give
explicit extensive bounds for the two interaction terms in
[Cam22, main.tex:1291-1298]. These are derived bounds for the actual operators,
with no numerical or asymptotic certificate supplied as a hypothesis.
-/

@[expose] public section

namespace QuantumAlg.FermiHubbard

open HilbertOperator JordanWigner

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

private lemma majorana_opNorm {n : ℕ} (j : Fin n × Fin 2) :
    opNorm (majoranaAt j : HilbertOperator (Qubits n)) = 1 :=
  opNorm_unitary (R := Qubits n) (majoranaAt j)

lemma kinetic_majorana_first_bound {L : ℕ} (hL : 2 ≤ L) (τ : ℝ)
    (j : Fin (2 * L ^ 2)) (a : Fin 2) :
    opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ ≤ 4 * |τ| := by
  rw [kinetic_lie_majoranaAt hL, opNorm_smul]
  have hs := opNorm_sum_le (fun d : Fin 4 =>
    (majoranaAt (kineticNeighbor j d, a.rev) : HilbertOperator (Qubits (2 * L ^ 2))))
  simp only [opNorm_unitary (R := Qubits (2 * L ^ 2)), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hs
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    hoppingMajoranaPhase_norm, mul_one]
  nlinarith [abs_nonneg τ]

lemma kinetic_majorana_second_bound {L : ℕ} (hL : 2 ≤ L) (τ : ℝ)
    (j : Fin (2 * L ^ 2)) (a : Fin 2) :
    opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
      (4 * |τ|) ^ 2 := by
  rw [kinetic_lie_majoranaAt hL]
  simp only [lie_smul, lie_sum, opNorm_smul, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, hoppingMajoranaPhase_norm, mul_one]
  have hs := opNorm_sum_le (fun d : Fin 4 =>
    ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (kineticNeighbor j d, a.rev) : HilbertOperator (Qubits (2 * L ^ 2)))⁆)
  have ht : (∑ d : Fin 4, opNorm
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (kineticNeighbor j d, a.rev) :
          HilbertOperator (Qubits (2 * L ^ 2)))⁆) ≤ 16 * |τ| := by
    calc
      _ ≤ ∑ _d : Fin 4, 4 * |τ| := Finset.sum_le_sum (fun d _ =>
        kinetic_majorana_first_bound hL τ (kineticNeighbor j d) a.rev)
      _ = _ := by simp; ring
  nlinarith [abs_nonneg τ]

lemma interaction_majorana_bounds {L : ℕ} (u : ℝ)
    (j : Fin (2 * L ^ 2)) (a : Fin 2) :
    opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ ≤ |u| / 2 ∧
    opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
      (|u| / 2) ^ 2 := by
  obtain ⟨⟨s, p⟩, rfl⟩ := (modeEquiv L).surjective j
  change opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ ≤ _ ∧ _
  constructor
  · rw [interaction_lie_majoranaAt, opNorm_smul, opNorm_unitary_mul_left,
      opNorm_unitary (R := Qubits (2 * L ^ 2))]
    simp [Complex.norm_real, Real.norm_eq_abs]
  · change opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (mode s p, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤ _
    rw [interaction_lie_twice_majoranaAt, opNorm_smul,
      opNorm_unitary (R := Qubits (2 * L ^ 2))]
    simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]

private lemma interaction_pair_bound {L : ℕ} (u : ℝ)
    (j k : Fin (2 * L ^ 2) × Fin 2) :
    opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt j : HilbertOperator (Qubits (2 * L ^ 2))) *
          (majoranaAt k : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤ |u| ^ 2 := by
  have h := Trotter.commutator_list_prod_bounds
    (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2)))
    (|u| / 2) (by positivity)
    [(majoranaAt j : HilbertOperator (Qubits (2 * L ^ 2))), majoranaAt k] (by
      intro X hX
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
      rcases hX with rfl | rfl
      · exact ⟨le_of_eq (opNorm_unitary (R := Qubits (2 * L ^ 2)) (majoranaAt j)),
          interaction_majorana_bounds u j.1 j.2⟩
      · exact ⟨le_of_eq (opNorm_unitary (R := Qubits (2 * L ^ 2)) (majoranaAt k)),
          interaction_majorana_bounds u k.1 k.2⟩)
  convert h.2.2 using 1 <;>
    simp only [List.prod_cons, List.prod_nil, mul_one, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.cast_ofNat]
  ring

lemma interaction_hopping_second_bound {L : ℕ} (u : ℝ)
    (p q : Fin (2 * L ^ 2)) (hpq : p ≠ q) :
    opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (hopping p q : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤ |u| ^ 2 := by
  rw [hopping_eq_majoranas p q hpq]
  simp only [lie_smul, lie_sub, opNorm_smul, norm_div, Complex.norm_I]
  have hp := interaction_pair_bound u (p, 0) (q, 1)
  have hq := interaction_pair_bound u (p, 1) (q, 0)
  have hs := opNorm_sub_le
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (p, 0) : HilbertOperator (Qubits (2 * L ^ 2))) *
          (majoranaAt (q, 1) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (p, 1) : HilbertOperator (Qubits (2 * L ^ 2))) *
          (majoranaAt (q, 0) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆
  rw [Complex.norm_ofNat]
  linarith

/-- The interaction-interaction-kinetic term has coefficient `4 L²`. -/
lemma interaction_kinetic_second_bound {L : ℕ} (hL : 2 ≤ L) (τ u : ℝ) :
    opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        (kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
      4 * (L : ℝ) ^ 2 * |u| ^ 2 * |τ| := by
  have hp (e : Equiv.Perm (Fin (2 * L ^ 2))) (he : ∀ p, p ≠ e p) :
      opNorm ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
          permutationHopping e⁆⁆ ≤ (2 * L ^ 2 : ℕ) * |u| ^ 2 := by
    simp only [permutationHopping, lie_sum]
    apply (opNorm_sum_le _).trans
    calc
      _ ≤ ∑ _p : Fin (2 * L ^ 2), |u| ^ 2 :=
        Finset.sum_le_sum (fun p _ => interaction_hopping_second_bound u p (e p) (he p))
      _ = _ := by simp
  have hh := hp (modePermutation (horizontalTranslation L))
    (modePermutation_ne_of_site_ne _ (fun p => (SquareTorus.right_ne_self hL p).symm))
  have hv := hp (modePermutation (verticalTranslation L))
    (modePermutation_ne_of_site_ne _ (fun p => (SquareTorus.down_ne_self hL p).symm))
  rw [kineticHamiltonian_eq_translations]
  simp only [lie_smul, lie_add, opNorm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hs := opNorm_add_le
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        permutationHopping (modePermutation (horizontalTranslation L))⁆⁆
    ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2))),
        permutationHopping (modePermutation (verticalTranslation L))⁆⁆
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hh hv
  nlinarith [abs_nonneg τ]

lemma kinetic_onsiteZZ_second_bound {L : ℕ} (hL : 2 ≤ L) (τ : ℝ) (p : Site L) :
    opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤ 256 * |τ| ^ 2 := by
  have hm (j : Fin (2 * L ^ 2)) (a : Fin 2) :
      opNorm (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2))) ≤ 1 ∧
      opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆ ≤ 4 * |τ| ∧
      opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
          (majoranaAt (j, a) : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
        (4 * |τ|) ^ 2 := by
    refine ⟨?_, kinetic_majorana_first_bound hL τ j a,
      kinetic_majorana_second_bound hL τ j a⟩
    exact le_of_eq (majorana_opNorm (n := 2 * L ^ 2) (j, a))
  have h := Trotter.commutator_list_prod_bounds
    (kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2)))
    (4 * |τ|) (by positivity)
    [(majoranaAt (mode 0 p, 0) : HilbertOperator (Qubits (2 * L ^ 2))),
      majoranaAt (mode 0 p, 1), majoranaAt (mode 1 p, 0), majoranaAt (mode 1 p, 1)] (by
        intro X hX
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
        rcases hX with rfl | rfl | rfl | rfl <;> exact hm _ _)
  rw [onsiteZZ_eq_majoranas]
  simp only [lie_neg, opNorm_neg]
  convert h.2.2 using 1 <;>
    simp only [List.prod_cons, List.prod_nil, mul_one, List.length_cons,
      List.length_nil, Nat.reduceAdd, Nat.cast_ofNat, mul_assoc]
  ring

/-- The kinetic-kinetic-interaction term has coefficient `64 L²`. -/
lemma kinetic_interaction_second_bound {L : ℕ} (hL : 2 ≤ L) (τ u : ℝ) :
    opNorm ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        (interactionHamiltonian L u : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
      64 * (L : ℝ) ^ 2 * |u| * |τ| ^ 2 := by
  rw [interactionHamiltonian_coe]
  simp only [lie_smul, lie_sum, opNorm_smul, norm_div, Complex.norm_real,
    Real.norm_eq_abs]
  have hs := opNorm_sum_le (fun p : Site L =>
    ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆)
  have ht : (∑ p : Site L, opNorm
      ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
        ⁅(kineticHamiltonian L τ : HilbertOperator (Qubits (2 * L ^ 2))),
          ((onsiteZZ p).op : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆) ≤
      (L : ℝ) ^ 2 * (256 * |τ| ^ 2) := by
    calc
      _ ≤ ∑ _p : Site L, 256 * |τ| ^ 2 :=
        Finset.sum_le_sum (fun p _ => kinetic_onsiteZZ_second_bound hL τ p)
      _ = _ := by simp [Site, SquareTorus.Site, pow_two, mul_assoc]
  have hscaled := mul_le_mul_of_nonneg_left (hs.trans ht)
    (div_nonneg (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 4))
  rw [Complex.norm_ofNat]
  nlinarith only [hscaled]

end

end QuantumAlg.FermiHubbard
