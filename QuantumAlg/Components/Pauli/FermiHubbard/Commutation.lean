/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.JordanWigner.Bilinears
import all QuantumAlg.Components.Pauli.JordanWigner.Commutation
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Core.Base.Hamiltonian
import Mathlib.Tactic

/-!
# Exact commutation within the plaquette decomposition

These identities follow from the canonical anticommutation relations, including
arbitrary Jordan–Wigner mode order and overlapping parity tails. A colour is a
sum of commuting complete plaquettes; its raw Pauli list need not commute.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- The spin and tile label, together with the corner, uniquely identify a mode. -/
lemma plaquette_corner_mode_injective {L : ℕ} (hL : Even L) (c : Fin 2) :
    Function.Injective (fun ax : PlaquetteLabel L × (Fin 2 × Fin 2) =>
      mode ax.1.1 (SquareTorus.corner c ax.1.2 ax.2)) := by
  rintro ⟨⟨s, a⟩, x⟩ ⟨⟨t, b⟩, y⟩ h
  obtain ⟨hst, hp⟩ := (mode_eq_iff s t _ _).mp h
  have hax : (a, x) = (b, y) := SquareTorus.corner_injective hL c hp
  cases hst
  cases hax
  rfl

/-- Distinct corner coordinates give distinct modes within a plaquette. -/
lemma plaquette_corner_modes_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    (a : PlaquetteLabel L) {x y : Fin 2 × Fin 2} (hxy : x ≠ y) :
    mode a.1 (SquareTorus.corner c a.2 x) ≠
      mode a.1 (SquareTorus.corner c a.2 y) := by
  intro h
  have heq : (a, x) = (a, y) := plaquette_corner_mode_injective hL c h
  exact hxy (congrArg Prod.snd heq)

/-- Distinct same-colour labels have disjoint physical fermionic modes. -/
lemma plaquette_modes_ne_of_label_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    {a b : PlaquetteLabel L} (hab : a ≠ b) (d e p f g q : Fin 2) :
    plaquetteMode c a d e p ≠ plaquetteMode c b f g q := by
  intro h
  have heq : (a, bondCorner d e p) = (b, bondCorner f g q) :=
    plaquette_corner_mode_injective hL c h
  exact hab (congrArg Prod.fst heq)

private lemma bondCorner_injective (d : Fin 2) :
    Function.Injective (fun ep : Fin 2 × Fin 2 => bondCorner d ep.1 ep.2) := by
  intro x y h
  by_cases hd : d = 0
  · simpa [bondCorner, hd] using h
  · simpa [bondCorner, hd, Prod.ext_iff, and_comm] using h

/-- Distinct endpoint labels within a matching give distinct modes. -/
lemma plaquette_matching_modes_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    (a : PlaquetteLabel L) (d : Fin 2) {e f p q : Fin 2}
    (h : (e, p) ≠ (f, q)) :
    plaquetteMode c a d e p ≠ plaquetteMode c a d f q :=
  plaquette_corner_modes_ne hL c a (fun heq => h (bondCorner_injective d heq))

/-- Each complete plaquette bond has distinct endpoints. -/
lemma plaquette_bond_modes_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    (a : PlaquetteLabel L) (d e : Fin 2) :
    plaquetteMode c a d e 0 ≠ plaquetteMode c a d e 1 :=
  plaquette_matching_modes_ne hL c a d (by simp)

/-- The two literal XX and YY entries of a bond commute, including zero coefficients. -/
lemma plaquetteBondTerms_pairwise {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d e : Fin 2) :
    (plaquetteBondTerms τ c a d e).terms.Pairwise (fun x y => x.2.Commute y.2) := by
  simpa [plaquetteBondTerms, hoppingTerms] using
    JordanWigner.hoppingString_xy_commute _ _ (plaquette_bond_modes_ne hL c a d e)

private lemma coe_signed_bond {n : ℕ} (τ : ℝ) (p q : Fin n) :
    (bondHamiltonian τ p q : HilbertOperator (Qubits n)) =
      ((-τ : ℝ) : ℂ) • (JordanWigner.hopping p q : HilbertOperator (Qubits n)) := rfl

private lemma signed_bonds_commute {n : ℕ} (τ : ℝ) (p q r s : Fin n)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    Commute (bondHamiltonian τ p q : HilbertOperator (Qubits n))
      (bondHamiltonian τ r s : HilbertOperator (Qubits n)) :=
  ((JordanWigner.hopping_commute_disjoint p q r s hpq hpr hps hqr hqs hrs).smul_left
    ((-τ : ℝ) : ℂ)).smul_right ((-τ : ℝ) : ℂ)

/-- Opposite complete bonds of either matching commute with their signed coefficients. -/
lemma plaquetteBond_commute {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d : Fin 2) (e f : Fin 2) (hef : e ≠ f) :
    Commute (plaquetteBond τ c a d e : HilbertOperator (Qubits (2 * L ^ 2)))
      (plaquetteBond τ c a d f : HilbertOperator (Qubits (2 * L ^ 2))) := by
  apply signed_bonds_commute
  · exact plaquette_bond_modes_ne hL c a d e
  · exact plaquette_matching_modes_ne hL c a d (by simp [hef])
  · exact plaquette_matching_modes_ne hL c a d (by simp [hef])
  · exact plaquette_matching_modes_ne hL c a d (by simp [hef])
  · exact plaquette_matching_modes_ne hL c a d (by simp [hef])
  · exact plaquette_bond_modes_ne hL c a d f

/-- Fin-indexed commutation of both complete bonds, including equal indices. -/
lemma plaquetteBond_pairwise {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d : Fin 2) :
    ∀ i j : Fin 2,
      Commute (plaquetteBond τ c a d i : HilbertOperator (Qubits (2 * L ^ 2)))
        (plaquetteBond τ c a d j : HilbertOperator (Qubits (2 * L ^ 2))) := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · exact plaquetteBond_commute hL τ c a d i j hij

/-- The two opposite-edge matchings commute exactly as complete fermionic operators. -/
lemma matchingHamiltonian_zero_one_commute {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L) :
    Commute (matchingHamiltonian τ c a 0 : HilbertOperator (Qubits (2 * L ^ 2)))
      (matchingHamiltonian τ c a 1 : HilbertOperator (Qubits (2 * L ^ 2))) := by
  let f (x : Fin 2 × Fin 2) := mode a.1 (SquareTorus.corner c a.2 x)
  have hne {x y : Fin 2 × Fin 2} (h : x ≠ y) : f x ≠ f y :=
    plaquette_corner_modes_ne hL c a h
  have h := JordanWigner.hopping_four_cycle_commute
    (f (0, 0)) (f (0, 1)) (f (1, 1)) (f (1, 0))
    (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide))
  rw [JordanWigner.hopping_symm (f (1, 1)) (f (1, 0)),
    JordanWigner.hopping_symm (f (1, 0)) (f (0, 0)),
    add_comm (JordanWigner.hopping (f (0, 1)) (f (1, 1)) :
      HilbertOperator (Qubits (2 * L ^ 2)))] at h
  have hs := (h.smul_left ((-τ : ℝ) : ℂ)).smul_right ((-τ : ℝ) : ℂ)
  simpa only [matchingHamiltonian, Hamiltonian.coe_sum, Fin.sum_univ_two,
    plaquetteBond, coe_signed_bond,
    plaquetteMode, bondCorner, Fin.zero_eta, ↓reduceIte, Fin.isValue,
    one_ne_zero, smul_add, f] using hs

/-- Fin-indexed exact commutation certificate for the two complete matchings. -/
lemma matchingHamiltonian_pairwise {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L) :
    ∀ i j : Fin 2,
      Commute (matchingHamiltonian τ c a i : HilbertOperator (Qubits (2 * L ^ 2)))
        (matchingHamiltonian τ c a j : HilbertOperator (Qubits (2 * L ^ 2))) := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact matchingHamiltonian_zero_one_commute hL τ c a
  · exact (matchingHamiltonian_zero_one_commute hL τ c a).symm
  · exact Commute.refl _

/-- Bonds in distinct same-colour plaquettes commute even if parity tails overlap. -/
lemma plaquetteBond_commute_of_label_ne {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) {a b : PlaquetteLabel L} (hab : a ≠ b) (d e f g : Fin 2) :
    Commute (plaquetteBond τ c a d e : HilbertOperator (Qubits (2 * L ^ 2)))
      (plaquetteBond τ c b f g : HilbertOperator (Qubits (2 * L ^ 2))) :=
  signed_bonds_commute τ _ _ _ _ (plaquette_bond_modes_ne hL c a d e)
    (plaquette_modes_ne_of_label_ne hL c hab d e 0 f g 0)
    (plaquette_modes_ne_of_label_ne hL c hab d e 0 f g 1)
    (plaquette_modes_ne_of_label_ne hL c hab d e 1 f g 0)
    (plaquette_modes_ne_of_label_ne hL c hab d e 1 f g 1)
    (plaquette_bond_modes_ne hL c b f g)

/-- Complete distinct plaquettes in one colour commute, also across spin sectors. -/
lemma plaquetteHamiltonian_commute {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) {a b : PlaquetteLabel L} (hab : a ≠ b) :
    Commute (plaquetteHamiltonian τ c a : HilbertOperator (Qubits (2 * L ^ 2)))
      (plaquetteHamiltonian τ c b : HilbertOperator (Qubits (2 * L ^ 2))) := by
  simp only [plaquetteHamiltonian, matchingHamiltonian, Hamiltonian.coe_sum]
  apply Commute.sum_left
  intro d _
  apply Commute.sum_left
  intro e _
  apply Commute.sum_right
  intro f _
  apply Commute.sum_right
  intro g _
  exact plaquetteBond_commute_of_label_ne hL τ c hab d e f g

/-- The fixed finite enumeration has no duplicate spin/tile labels. -/
lemma plaquetteAt_injective (L : ℕ) : Function.Injective (plaquetteAt L) :=
  (modeEquiv (L / 2)).symm.injective

/-- Fin-indexed commutation of the complete plaquettes of one colour. -/
lemma plaquetteHamiltonian_pairwise {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2) :
    ∀ i j : Fin (2 * (L / 2) ^ 2),
      Commute (plaquetteHamiltonian τ c (plaquetteAt L i) :
        HilbertOperator (Qubits (2 * L ^ 2)))
        (plaquetteHamiltonian τ c (plaquetteAt L j) :
          HilbertOperator (Qubits (2 * L ^ 2))) := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · exact plaquetteHamiltonian_commute hL τ c
      (fun h => hij (plaquetteAt_injective L h))

/-- Each complete signed plaquette bond conserves total particle number. -/
lemma totalNumber_commute_plaquetteBond {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L) (d e : Fin 2) :
    Commute (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2)))
      (plaquetteBond τ c a d e : HilbertOperator (Qubits (2 * L ^ 2))) :=
  (JordanWigner.totalNumber_commute_hopping _ _
    (plaquette_bond_modes_ne hL c a d e)).smul_right ((-τ : ℝ) : ℂ)

/-- Each complete matching conserves total particle number. -/
lemma totalNumber_commute_matchingHamiltonian {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L) (d : Fin 2) :
    Commute (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2)))
      (matchingHamiltonian τ c a d : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [matchingHamiltonian, Hamiltonian.coe_sum]
  exact Commute.sum_right _ _ _ (fun e _ => totalNumber_commute_plaquetteBond hL τ c a d e)

/-- Each complete plaquette conserves total particle number. -/
lemma totalNumber_commute_plaquetteHamiltonian {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) (a : PlaquetteLabel L) :
    Commute (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2)))
      (plaquetteHamiltonian τ c a : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [plaquetteHamiltonian, Hamiltonian.coe_sum]
  exact Commute.sum_right _ _ _ (fun d _ => totalNumber_commute_matchingHamiltonian hL τ c a d)

/-- The full Hamiltonian of either colour conserves total particle number. -/
lemma totalNumber_commute_colourHamiltonian {L : ℕ} (hL : Even L)
    (τ : ℝ) (c : Fin 2) :
    Commute (JordanWigner.totalNumber (2 * L ^ 2) : HilbertOperator (Qubits (2 * L ^ 2)))
      (colourHamiltonian L τ c : HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [colourHamiltonian, Hamiltonian.coe_sum]
  exact Commute.sum_right _ _ _ (fun j _ =>
    totalNumber_commute_plaquetteHamiltonian hL τ c (plaquetteAt L j))

end
end QuantumAlg.FermiHubbard
