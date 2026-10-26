/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Pauli.FermiHubbard.Local.Kinetic
public import QuantumAlg.Components.Pauli.FermiHubbard.Commutation
public import QuantumAlg.Components.Pauli.JordanWigner.MatchingBounds
public import QuantumAlg.Util.Lattice.SquareTorus.Matchings
import all QuantumAlg.Components.Pauli.FermiHubbard.Local.Kinetic
import all QuantumAlg.Components.Pauli.FermiHubbard.Plaquettes
import all QuantumAlg.Components.Pauli.FermiHubbard.Commutation
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.JordanWigner.MatchingBounds
import all QuantumAlg.Components.Pauli.JordanWigner.Permutations
import all QuantumAlg.Components.Pauli.JordanWigner.Bilinears
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Util.Lattice.SquareTorus.Matchings
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import Mathlib.Tactic

/-!
# Complete matching cancellation for the actual plaquette colors

Each original color is the sum of one horizontal and one vertical perfect
matching. Cross-coordinate commutation leaves two one-dimensional nested
commutators, giving an explicit extensive bound for
[Cam22, main.tex:1307-1317].
-/

@[expose] public section

namespace QuantumAlg.FermiHubbard

open HilbertOperator JordanWigner

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The horizontal matching of one color, in the fixed physical mode encoding. -/
def colourHorizontal {L : ℕ} (hL : Even L) (c : Fin 2) :
    Equiv.Perm (Fin (2 * L ^ 2)) :=
  modePermutation (SquareTorus.horizontalMatching hL c)

/-- The vertical matching of one color, in the fixed physical mode encoding. -/
def colourVertical {L : ℕ} (hL : Even L) (c : Fin 2) :
    Equiv.Perm (Fin (2 * L ^ 2)) :=
  modePermutation (SquareTorus.verticalMatching hL c)

private lemma permutationBilinear_eq_site_sum {L : ℕ} (e : Equiv.Perm (Site L)) :
    permutationBilinear (modePermutation e) =
      ∑ s : Fin 2, ∑ p : Site L, bilinear (mode s p) (mode s (e p)) := by
  rw [permutationBilinear, ← (modeEquiv L).sum_comp
    (fun j => bilinear j (modePermutation e j))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro p _
  change bilinear (mode s p) (modePermutation e (mode s p)) = _
  rw [modePermutation_mode]

private lemma horizontal_bilinear_eq_bonds {L : ℕ} (hL : Even L) (c : Fin 2) :
    permutationBilinear (colourHorizontal hL c) =
      ∑ s : Fin 2, ∑ a : SquareTorus.Tile L, ∑ b : Fin 2,
        (hopping (plaquetteMode c (s, a) 0 b 0) (plaquetteMode c (s, a) 0 b 1) :
          HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [colourHorizontal, permutationBilinear_eq_site_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← (SquareTorus.cornerEquiv hL c).sum_comp (fun p =>
    bilinear (mode s p) (mode s (SquareTorus.horizontalMatching hL c p)))]
  rw [Fintype.sum_prod_type]
  simp only [SquareTorus.cornerEquiv, Equiv.coe_fn_mk, SquareTorus.horizontalMatching_corner]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.sum_univ_two]
  rw [hopping_eq_ladders _ _ (plaquette_bond_modes_ne hL c (s, a) 0 b)]
  simp [bilinear, plaquetteMode, bondCorner]

private lemma vertical_bilinear_eq_bonds {L : ℕ} (hL : Even L) (c : Fin 2) :
    permutationBilinear (colourVertical hL c) =
      ∑ s : Fin 2, ∑ a : SquareTorus.Tile L, ∑ b : Fin 2,
        (hopping (plaquetteMode c (s, a) 1 b 0) (plaquetteMode c (s, a) 1 b 1) :
          HilbertOperator (Qubits (2 * L ^ 2))) := by
  rw [colourVertical, permutationBilinear_eq_site_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← (SquareTorus.cornerEquiv hL c).sum_comp (fun p =>
    bilinear (mode s p) (mode s (SquareTorus.verticalMatching hL c p)))]
  rw [Fintype.sum_prod_type]
  simp only [SquareTorus.cornerEquiv, Equiv.coe_fn_mk, SquareTorus.verticalMatching_corner]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fin.sum_univ_two]
  rw [hopping_eq_ladders _ _ (plaquette_bond_modes_ne hL c (s, a) 1 b)]
  simp [bilinear, plaquetteMode, bondCorner]

/-- This is an equality with the original complete plaquette operator. -/
lemma colourHamiltonian_eq_matchings {L : ℕ} (hL : Even L) (τ : ℝ) (c : Fin 2) :
    (colourHamiltonian L τ c : HilbertOperator (Qubits (2 * L ^ 2))) =
      (-τ : ℂ) •
        (permutationBilinear (colourHorizontal hL c) +
          permutationBilinear (colourVertical hL c)) := by
  have hb (p q : Fin (2 * L ^ 2)) :
      (bondHamiltonian τ p q : HilbertOperator (Qubits (2 * L ^ 2))) =
        (-τ : ℂ) • (hopping p q : HilbertOperator (Qubits (2 * L ^ 2))) := by
    change (((-τ : ℝ) : ℂ) • (hopping p q : HilbertOperator (Qubits (2 * L ^ 2)))) = _
    rw [Complex.ofReal_neg]
  rw [horizontal_bilinear_eq_bonds, vertical_bilinear_eq_bonds]
  simp only [colourHamiltonian, Hamiltonian.coe_sum]
  rw [sum_plaquetteAt (fun a : PlaquetteLabel L =>
    (plaquetteHamiltonian τ c a : HilbertOperator (Qubits (2 * L ^ 2))))]
  simp only [Fintype.sum_prod_type, plaquetteHamiltonian, matchingHamiltonian,
    Hamiltonian.coe_sum, plaquetteBond, hb, ← Finset.smul_sum]
  congr 1
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  abel

lemma colourHorizontal_twice {L : ℕ} (hL : Even L) (c : Fin 2)
    (j : Fin (2 * L ^ 2)) : colourHorizontal hL c (colourHorizontal hL c j) = j := by
  obtain ⟨⟨s, p⟩, rfl⟩ := (modeEquiv L).surjective j
  change colourHorizontal hL c (colourHorizontal hL c (mode s p)) = mode s p
  simp [colourHorizontal]

lemma colourVertical_twice {L : ℕ} (hL : Even L) (c : Fin 2)
    (j : Fin (2 * L ^ 2)) : colourVertical hL c (colourVertical hL c j) = j := by
  obtain ⟨⟨s, p⟩, rfl⟩ := (modeEquiv L).surjective j
  change colourVertical hL c (colourVertical hL c (mode s p)) = mode s p
  simp [colourVertical]

lemma colourHorizontal_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    (j : Fin (2 * L ^ 2)) : j ≠ colourHorizontal hL c j :=
  modePermutation_ne_of_site_ne _ (SquareTorus.horizontalMatching_ne hL c) j

lemma colourVertical_ne {L : ℕ} (hL : Even L) (c : Fin 2)
    (j : Fin (2 * L ^ 2)) : j ≠ colourVertical hL c j :=
  modePermutation_ne_of_site_ne _ (SquareTorus.verticalMatching_ne hL c) j

lemma colour_horizontal_vertical_commute {L : ℕ} (hL : Even L) (c d : Fin 2)
    (j : Fin (2 * L ^ 2)) :
    colourHorizontal hL c (colourVertical hL d j) =
      colourVertical hL d (colourHorizontal hL c j) := by
  obtain ⟨⟨s, p⟩, rfl⟩ := (modeEquiv L).surjective j
  change colourHorizontal hL c (colourVertical hL d (mode s p)) =
    colourVertical hL d (colourHorizontal hL c (mode s p))
  simp only [colourHorizontal, colourVertical, modePermutation_mode]
  rw [SquareTorus.horizontal_vertical_matching_commute]

/-- Either ordering of two colors has the required complete-matching bound. -/
lemma colour_nested_opNorm_le {L : ℕ} (hL : Even L) (τ : ℝ) (c d : Fin 2) :
    opNorm ⁅(colourHamiltonian L τ d : HilbertOperator (Qubits (2 * L ^ 2))),
      ⁅(colourHamiltonian L τ d : HilbertOperator (Qubits (2 * L ^ 2))),
        (colourHamiltonian L τ c : HilbertOperator (Qubits (2 * L ^ 2)))⁆⁆ ≤
      8 * (L : ℝ) ^ 2 * |τ| ^ 3 := by
  have h := two_matchings_nested_opNorm_le
    (colourHorizontal hL c) (colourVertical hL c)
    (colourHorizontal hL d) (colourVertical hL d)
    (colourHorizontal_twice hL c) (colourVertical_twice hL c)
    (colourHorizontal_twice hL d) (colourVertical_twice hL d)
    (colourHorizontal_ne hL c) (colourVertical_ne hL c)
    (colour_horizontal_vertical_commute hL d c)
    (fun p => (colour_horizontal_vertical_commute hL c d p).symm)
    (colour_horizontal_vertical_commute hL d d)
  simp only [colourHamiltonian_eq_matchings hL, smul_lie, lie_smul, smul_smul,
    opNorm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hs := mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg τ) 3)
  nlinarith only [hs]

end

end QuantumAlg.FermiHubbard
