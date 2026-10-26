/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Util.Lattice.SquareTorus
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
public import QuantumAlg.Components.Pauli.JordanWigner
import all QuantumAlg.Components.Pauli.JordanWigner.Strings

/-!
# Spin-separated snake modes

The first L² modes have spin up and the next L² have spin down. Each spin
sector uses a row-snake order, with position zero the most-significant qubit.
The Jordan-Wigner algebra uses the explicit prefix convention of
[WBA11, h2.arxiv2.tex:329-346].
-/

public section
namespace QuantumAlg.FermiHubbard

/-- A physical site of the square lattice. -/
abbrev Site (L : ℕ) := SquareTorus.Site L

/-- Complete spin-separated mode indexing. -/
@[expose] def modeEquiv (L : ℕ) : (Fin 2 × Site L) ≃ Fin (2 * L ^ 2) :=
  (Equiv.prodCongr (Equiv.refl _) (SquareTorus.snakeEquiv L)).trans finProdFinEquiv

/-- The qubit position of a spin and physical site. -/
@[expose] def mode {L : ℕ} (spin : Fin 2) (p : Site L) : Fin (2 * L ^ 2) :=
  modeEquiv L (spin, p)

lemma mode_val {L : ℕ} (spin : Fin 2) (p : Site L) :
    (mode spin p).val = (SquareTorus.snakeIndex p).val + L ^ 2 * spin.val := by
  simp [mode, modeEquiv, finProdFinEquiv]

lemma mode_eq_iff {L : ℕ} (s t : Fin 2) (p q : Site L) :
    mode s p = mode t q ↔ s = t ∧ p = q := by
  change modeEquiv L (s, p) = modeEquiv L (t, q) ↔ _
  rw [(modeEquiv L).injective.eq_iff, Prod.mk.injEq]

lemma mode_ne_of_site_ne {L : ℕ} (spin : Fin 2) {p q : Site L} (hpq : p ≠ q) :
    mode spin p ≠ mode spin q := by
  intro h
  exact hpq ((mode_eq_iff spin spin p q).mp h).2

lemma mode_ne_of_spin_ne {L : ℕ} {s t : Fin 2} (hst : s ≠ t) (p q : Site L) :
    mode s p ≠ mode t q := by
  intro h
  exact hst ((mode_eq_iff s t p q).mp h).1

/-- Adding the spin-sector offset preserves all within-sector distances. -/
lemma mode_distance {L : ℕ} (spin : Fin 2) (p q : Site L) :
    Nat.dist (mode spin p).val (mode spin q).val =
      Nat.dist (SquareTorus.snakeIndex p).val (SquareTorus.snakeIndex q).val := by
  rw [mode_val, mode_val, Nat.dist_add_add_right]

/-- A concrete ordering of all sites, inverse to the row-snake index. -/
@[expose] def siteAt (L : ℕ) (j : Fin (L ^ 2)) : Site L :=
  (SquareTorus.snakeEquiv L).symm j

lemma sum_siteAt {L : ℕ} {M : Type*} [AddCommMonoid M] (f : Site L → M) :
    (∑ j : Fin (L ^ 2), f (siteAt L j)) = ∑ p : Site L, f p :=
  Equiv.sum_comp (SquareTorus.snakeEquiv L).symm f

end QuantumAlg.FermiHubbard
