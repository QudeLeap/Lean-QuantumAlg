/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
public import QuantumAlg.Components.Pauli.FermiHubbard.Model
public import QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Components.Pauli.FermiHubbard.Diagonal
import all QuantumAlg.Components.Pauli.FermiHubbard.Onsite
import all QuantumAlg.Components.Pauli.FermiHubbard.Model
import all QuantumAlg.Components.Pauli.FermiHubbard.Modes
import all QuantumAlg.Components.Pauli.Sum.Family
import all QuantumAlg.Components.Pauli.Sum
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Util.Lattice.SquareTorus.Distances
import all QuantumAlg.Primitives.Trotter.Circuit.Term
import all QuantumAlg.Primitives.Trotter.Circuit.Cost
import all QuantumAlg.Primitives.Trotter.PauliRotation.Cost
import all QuantumAlg.Components.Gates.GlobalPhase

/-!
# Native Hubbard term costs

Every literal Pauli entry is compiled by the existing native term circuit.
Periodic strings contribute their full row-snake length. Zero coefficients
retain the same visits, and each per-site identity contributes one scalar phase.
The formulas are derived from emitted leaves, not from a synthesized T count.
-/

public section
namespace QuantumAlg.FermiHubbard
noncomputable section

open Trotter

/-- Exact pool of all entries in one full Hubbard pass. -/
@[expose] def nativePassPool (L : ℕ) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  (16 * L * (L - 1) * (L + 1) + 2 * L ^ 2) • {.gate .cnot} +
  (11 * L ^ 2) • {.gate .singleQubit} +
  (32 * L ^ 2) • {.gate .singleQubit} +
  (32 * L ^ 2) • {.gate .singleQubit} +
  L ^ 2 • {.gate .singleQubit}

private lemma diagonal_letterCount {n : ℕ} (P : PauliString n)
    (hP : ∀ j, P j = .i ∨ P j = .z) (a : PauliLetter) (ha : a = .x ∨ a = .y) :
    pauliLetterCount P a = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  rcases hP j with hp | hp <;> rcases ha with rfl | rfl <;> simp_all

private lemma siteTerms_termPool {L : ℕ} (u μ : ℝ) (p : Site L) :
    ((siteTerms u μ p).terms.map termPool).sum =
      2 • ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
      3 • {.gate .singleQubit} +
      {.gate .singleQubit} := by
  have hZZ (j : Fin (2 * L ^ 2)) : onsiteZZ p j = .i ∨ onsiteZZ p j = .z := by
    rw [onsiteZZ_apply]
    split_ifs <;> simp
  have hZ (q : Fin (2 * L ^ 2)) (j : Fin (2 * L ^ 2)) :
      JordanWigner.modeZ q j = .i ∨ JordanWigner.modeZ q j = .z := by
    simp only [JordanWigner.modeZ]
    split_ifs <;> simp
  simp only [siteTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    termPool, onsiteZZ_support, modeZ_support, identityString_support,
    Finset.insert_nonempty, Finset.singleton_nonempty, Finset.not_nonempty_empty,
    ↓reduceIte, onsiteZZ_weight, modeZ_weight,
    diagonal_letterCount _ hZZ .x (Or.inl rfl),
    diagonal_letterCount _ hZZ .y (Or.inr rfl),
    diagonal_letterCount _ (hZ _) .x (Or.inl rfl),
    diagonal_letterCount _ (hZ _) .y (Or.inr rfl)]
  norm_num
  simp only [← Multiset.singleton_add]
  abel

/-- One complete hopping bond counts both endpoint flavors and the full parity chain. -/
lemma hoppingTerms_termPool {n : ℕ} (τ : ℝ) (p q : Fin n) (hpq : p ≠ q) :
    ((hoppingTerms τ p q).terms.map termPool).sum =
      (4 * Nat.dist p.val q.val) •
        ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
      2 • {.gate .singleQubit} +
      8 • {.gate .singleQubit} + 8 • {.gate .singleQubit} := by
  have hne (a : PauliLetter) (ha : a = .x ∨ a = .y) :
      (JordanWigner.hoppingString p q a).support.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (JordanWigner.hoppingString p q a).weight
    rw [JordanWigner.hoppingString_weight p q a ha]
    omega
  simp only [hoppingTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    termPool, hne .x (Or.inl rfl), hne .y (Or.inr rfl), ↓reduceIte,
    JordanWigner.hoppingString_weight p q .x (Or.inl rfl),
    JordanWigner.hoppingString_weight p q .y (Or.inr rfl), pauliLetterCount,
    JordanWigner.hoppingString_endpoint_count p q hpq .x (Or.inl rfl),
    JordanWigner.hoppingString_endpoint_count p q hpq .y (Or.inr rfl),
    JordanWigner.hoppingString_other_count p q .x .y
      (Or.inl rfl) (Or.inr rfl) (by decide),
    JordanWigner.hoppingString_other_count p q .y .x
      (Or.inr rfl) (Or.inl rfl) (by decide)]
  norm_num
  rw [show 4 * Nat.dist p.val q.val =
    2 * Nat.dist p.val q.val + 2 * Nat.dist p.val q.val by omega, add_nsmul]
  abel

/-- All on-site native visits, including one scalar phase at each site. -/
lemma onsite_termPool (L : ℕ) (u μ : ℝ) :
    ((onsite L u μ).terms.map termPool).sum =
      (2 * L ^ 2) • ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
      (3 * L ^ 2) • {.gate .singleQubit} +
      L ^ 2 • {.gate .singleQubit} := by
  rw [onsite, PauliSum.ofFamily_sum_terms]
  simp only [siteTerms_termPool, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_add, smul_smul]
  simp only [Nat.mul_comm]

/-- Both spin sectors include every periodic positive-direction bond. -/
lemma kineticTerms_termPool {L : ℕ} (hL : 2 ≤ L) (τ : ℝ) :
    ((kineticTerms L τ).terms.map termPool).sum =
      (16 * L * (L - 1) * (L + 1)) •
        ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
      (8 * L ^ 2) • {.gate .singleQubit} +
      (32 * L ^ 2) • {.gate .singleQubit} +
      (32 * L ^ 2) • {.gate .singleQubit} := by
  rw [kineticTerms, PauliSum.ofFamily_sum_terms]
  have hs (s : Fin 2) :
      ((PauliSum.ofFamily fun j : Fin (L ^ 2) =>
        siteHoppingTerms τ s (siteAt L j)).terms.map termPool).sum =
      ∑ p : Site L, ((4 *
        (Nat.dist (SquareTorus.snakeIndex p).val
          (SquareTorus.snakeIndex (SquareTorus.right p)).val +
        Nat.dist (SquareTorus.snakeIndex p).val
          (SquareTorus.snakeIndex (SquareTorus.down p)).val)) •
        ({.gate .cnot} : ResourcePool (.quantum AlgorithmGate.model .empty)) +
        4 • {.gate .singleQubit} +
        16 • {.gate .singleQubit} + 16 • {.gate .singleQubit}) := by
    rw [PauliSum.ofFamily_sum_terms,
      sum_siteAt (fun p => ((siteHoppingTerms τ s p).terms.map termPool).sum)]
    apply Finset.sum_congr rfl
    intro p _
    simp only [siteHoppingTerms, PauliSum.pauliSum_terms_add, List.map_append,
      List.sum_append, hoppingTerms_termPool _ _ _ (horizontal_modes_ne hL s p),
      hoppingTerms_termPool _ _ _ (vertical_modes_ne hL s p), mode_distance,
      Nat.mul_add, add_nsmul]
    abel
  simp only [hs, Finset.sum_add_distrib, ← Finset.sum_smul,
    ← Finset.mul_sum, SquareTorus.sum_snake_bond_distances hL, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have h8 : 4 * (2 * L * (L - 1) * (2 * L + 2 * 1)) =
      16 * L * (L - 1) * (L + 1) := by ring
  have h32 : L * L * (2 * 16) = 32 * L ^ 2 := by ring
  have hR : L * L * (2 * 4) = 8 * L ^ 2 := by ring
  simp only [h8, h32, hR]

/-- Closed native counts belong to the actual list of full-model term circuits. -/
lemma pauliSum_passPool {L : ℕ} (hL : 2 ≤ L) (τ u μ : ℝ) :
    passPool (pauliSum L τ u μ) = nativePassPool L := by
  rw [← sum_termPool, pauliSum, PauliSum.pauliSum_terms_add, List.map_append,
    List.sum_append, onsite_termPool, kineticTerms_termPool hL]
  simp only [nativePassPool, add_nsmul]
  have hr : 11 * L ^ 2 = 3 * L ^ 2 + 8 * L ^ 2 := by omega
  rw [hr, add_nsmul]
  abel

end
end QuantumAlg.FermiHubbard
