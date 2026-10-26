/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Util.Lattice.SquareTorus.Edges
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Core.Base.Hamiltonian

/-!
# Two colours of periodic plaquettes

Each colour partitions the sites into two-by-two tiles, independently in each
spin sector. The two colours together cover every positive horizontal and
vertical bond exactly once. These identities concern complete plaquettes;
the raw Pauli list of a colour is not internally commuting.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

/-- One spin sector and one physical tile. -/
abbrev PlaquetteLabel (L : ℕ) := Fin 2 × SquareTorus.Tile L

/-- Fixed spin-separated ordering of the tiles of one colour. -/
@[expose] def plaquetteAt (L : ℕ) (j : Fin (2 * (L / 2) ^ 2)) : PlaquetteLabel L :=
  (modeEquiv (L / 2)).symm j

lemma sum_plaquetteAt {L : ℕ} {M : Type*} [AddCommMonoid M]
    (f : PlaquetteLabel L → M) :
    (∑ j, f (plaquetteAt L j)) = ∑ a, f a :=
  Equiv.sum_comp (modeEquiv (L / 2)).symm f

/-- Corners at the ends of the two edges in either opposite-edge matching. -/
@[expose] def bondCorner (direction edge endpoint : Fin 2) : Fin 2 × Fin 2 :=
  if direction = 0 then (edge, endpoint) else (endpoint, edge)

/-- A physical mode at an endpoint of a coloured plaquette edge. -/
@[expose] def plaquetteMode {L : ℕ} (colour : Fin 2) (a : PlaquetteLabel L)
    (direction edge endpoint : Fin 2) : Fin (2 * L ^ 2) :=
  mode a.1 (SquareTorus.corner colour a.2 (bondCorner direction edge endpoint))

/-- The two hopping strings of one plaquette edge. -/
@[expose] def plaquetteBondTerms {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) (direction edge : Fin 2) : PauliSum (2 * L ^ 2) :=
  hoppingTerms τ (plaquetteMode colour a direction edge 0)
    (plaquetteMode colour a direction edge 1)

/-- Two disjoint edges of one plaquette, preserving both flavors per bond. -/
@[expose] def matchingTerms {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) (direction : Fin 2) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun edge : Fin 2 => plaquetteBondTerms τ colour a direction edge)

/-- Four bonds of a plaquette, ordered as its two complete matchings. -/
@[expose] def plaquetteTerms {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun direction : Fin 2 => matchingTerms τ colour a direction)

/-- All exact plaquettes of one colour, in a fixed spin/tile order. -/
@[expose] def colourTerms (L : ℕ) (τ : ℝ) (colour : Fin 2) : PauliSum (2 * L ^ 2) :=
  PauliSum.ofFamily (fun j => plaquetteTerms τ colour (plaquetteAt L j))

/-- A complete signed edge operator. -/
@[expose] def plaquetteBond {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) (direction edge : Fin 2) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  bondHamiltonian τ (plaquetteMode colour a direction edge 0)
    (plaquetteMode colour a direction edge 1)

/-- The Hamiltonian of two opposite edges. -/
@[expose] def matchingHamiltonian {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) (direction : Fin 2) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.sum (fun edge : Fin 2 => plaquetteBond τ colour a direction edge)

/-- The Hamiltonian of a complete four-cycle. -/
@[expose] def plaquetteHamiltonian {L : ℕ} (τ : ℝ) (colour : Fin 2)
    (a : PlaquetteLabel L) : Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.sum (fun direction : Fin 2 => matchingHamiltonian τ colour a direction)

/-- The sum of all complete plaquettes of one colour. -/
@[expose] def colourHamiltonian (L : ℕ) (τ : ℝ) (colour : Fin 2) :
    Hamiltonian (Qubits (2 * L ^ 2)) :=
  Hamiltonian.sum (fun j => plaquetteHamiltonian τ colour (plaquetteAt L j))

lemma matchingTerms_toHamiltonian {L : ℕ} (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) (d : Fin 2) :
    (matchingTerms τ c a d).toHamiltonian = matchingHamiltonian τ c a d := by
  simp only [matchingTerms, PauliSum.ofFamily_toHamiltonian, plaquetteBondTerms,
    hoppingTerms_toHamiltonian, matchingHamiltonian, plaquetteBond]

lemma plaquetteTerms_toHamiltonian {L : ℕ} (τ : ℝ) (c : Fin 2)
    (a : PlaquetteLabel L) :
    (plaquetteTerms τ c a).toHamiltonian = plaquetteHamiltonian τ c a := by
  simp only [plaquetteTerms, PauliSum.ofFamily_toHamiltonian,
    matchingTerms_toHamiltonian, plaquetteHamiltonian]

lemma colourTerms_toHamiltonian (L : ℕ) (τ : ℝ) (c : Fin 2) :
    (colourTerms L τ c).toHamiltonian = colourHamiltonian L τ c := by
  simp only [colourTerms, PauliSum.ofFamily_toHamiltonian,
    plaquetteTerms_toHamiltonian, colourHamiltonian]

/-- Every occurrence has the original positive horizontal orientation. -/
lemma plaquetteBondTerms_horizontal {L : ℕ} (τ : ℝ) (c s : Fin 2)
    (a : SquareTorus.Tile L) (b : Fin 2) :
    plaquetteBondTerms τ c (s, a) 0 b =
      hoppingTerms τ (mode s (SquareTorus.horizontalStart c a b))
        (mode s (SquareTorus.right (SquareTorus.horizontalStart c a b))) := by
  rw [SquareTorus.right_horizontalStart]
  simp [plaquetteBondTerms, plaquetteMode, bondCorner, SquareTorus.horizontalStart]

/-- Every occurrence has the original positive vertical orientation. -/
lemma plaquetteBondTerms_vertical {L : ℕ} (τ : ℝ) (c s : Fin 2)
    (a : SquareTorus.Tile L) (b : Fin 2) :
    plaquetteBondTerms τ c (s, a) 1 b =
      hoppingTerms τ (mode s (SquareTorus.verticalStart c a b))
        (mode s (SquareTorus.down (SquareTorus.verticalStart c a b))) := by
  rw [SquareTorus.down_verticalStart]
  simp [plaquetteBondTerms, plaquetteMode, bondCorner, SquareTorus.verticalStart]

/-- The two colours preserve every term statistic that is additive over the list.
This certifies both operator coverage and literal event-count coverage. -/
lemma colourTerms_sum_terms {L : ℕ} (hL : Even L) (τ : ℝ)
    {M : Type*} [AddCommMonoid M] (f : ℝ × PauliString (2 * L ^ 2) → M) :
    (∑ c : Fin 2, ((colourTerms L τ c).terms.map f).sum) =
      ((kineticTerms L τ).terms.map f).sum := by
  have hc (c : Fin 2) : ((colourTerms L τ c).terms.map f).sum =
      ∑ s : Fin 2, ∑ a : SquareTorus.Tile L, ∑ d : Fin 2, ∑ b : Fin 2,
        ((plaquetteBondTerms τ c (s, a) d b).terms.map f).sum := by
    rw [colourTerms, PauliSum.ofFamily_sum_terms,
      sum_plaquetteAt (fun a => ((plaquetteTerms τ c a).terms.map f).sum)]
    simp only [Fintype.sum_prod_type, plaquetteTerms, matchingTerms,
      PauliSum.ofFamily_sum_terms]
  simp_rw [hc]
  rw [show ((kineticTerms L τ).terms.map f).sum =
    ∑ s : Fin 2, ∑ p : Site L,
      (((hoppingTerms τ (mode s p) (mode s (SquareTorus.right p))).terms.map f).sum +
      ((hoppingTerms τ (mode s p) (mode s (SquareTorus.down p))).terms.map f).sum) by
        simp only [kineticTerms, PauliSum.ofFamily_sum_terms, siteHoppingTerms,
          PauliSum.pauliSum_terms_add, List.map_append, List.sum_append]
        apply Finset.sum_congr rfl
        intro s _
        exact sum_siteAt (L := L) (fun p =>
          ((hoppingTerms τ (mode s p) (mode s (SquareTorus.right p))).terms.map f).sum +
          ((hoppingTerms τ (mode s p) (mode s (SquareTorus.down p))).terms.map f).sum)]
  have hh (s : Fin 2) := SquareTorus.sum_horizontalStart hL
    (fun p : Site L =>
      ((hoppingTerms τ (mode s p) (mode s (SquareTorus.right p))).terms.map f).sum)
  have hv (s : Fin 2) := SquareTorus.sum_verticalStart hL
    (fun p : Site L =>
      ((hoppingTerms τ (mode s p) (mode s (SquareTorus.down p))).terms.map f).sum)
  simp only [Fin.sum_univ_two, plaquetteBondTerms_horizontal,
    plaquetteBondTerms_vertical, Finset.sum_add_distrib] at hh hv ⊢
  rw [← hh 0, ← hh 1, ← hv 0, ← hv 1]
  abel

/-- The original kinetic operator is the sum of the two complete colours. -/
lemma colourHamiltonian_sum {L : ℕ} (hL : Even L) (τ : ℝ) :
    Hamiltonian.sum (colourHamiltonian L τ) = kineticHamiltonian L τ := by
  apply Hamiltonian.ext
  simp only [Hamiltonian.coe_sum, ← colourTerms_toHamiltonian,
    ← kineticTerms_toHamiltonian, PauliSum.coe_toHamiltonian]
  exact colourTerms_sum_terms hL τ
    (fun term => (PauliSum.termHamiltonian term : HilbertOperator (Qubits (2 * L ^ 2))))

end
end QuantumAlg.FermiHubbard
