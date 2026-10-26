/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.String
import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Jordan–Wigner Pauli strings

We use a Z prefix, equivalently reversing the mode order of the Z suffix in
[WBA11, h2.arxiv2.tex:329]. The ladder convention is the one in
[WBA11, h2.arxiv2.tex:346]. Position zero is the most-significant qubit.
-/

public section
namespace QuantumAlg.JordanWigner

/-- A Z prefix followed by an X or Y Majorana endpoint. -/
@[expose] def majoranaString {n : ℕ} (p : Fin n) (letter : PauliLetter) : PauliString n :=
  fun j => if j = p then letter else if j < p then .z else .i

/-- A singleton Z at one fermionic mode. -/
@[expose] def modeZ {n : ℕ} (p : Fin n) : PauliString n :=
  fun j => if j = p then .z else .i

/-- Two endpoint letters with Z strictly between the endpoints. -/
@[expose] def hoppingString {n : ℕ} (p q : Fin n) (letter : PauliLetter) : PauliString n :=
  fun j => if j = p ∨ j = q then letter
    else if min p q < j ∧ j < max p q then .z else .i

/-- Reversing the bond preserves its Pauli string. -/
lemma hoppingString_symm {n : ℕ} (p q : Fin n) (letter : PauliLetter) :
    hoppingString p q letter = hoppingString q p letter := by
  funext j
  simp only [hoppingString, or_comm, min_comm, max_comm]

/-- An X/Y string occupies exactly its closed endpoint interval. -/
lemma hoppingString_support {n : ℕ} (p q : Fin n) (letter : PauliLetter)
    (hl : letter = .x ∨ letter = .y) :
    (hoppingString p q letter).support = Finset.Icc (min p q) (max p q) := by
  ext j
  simp only [PauliString.support, Finset.mem_filter_univ, Finset.mem_Icc]
  rcases hl with rfl | rfl <;> simp only [hoppingString] <;>
    split_ifs <;> simp_all <;> omega

/-- The number of occupied qubits is endpoint distance plus one. -/
lemma hoppingString_weight {n : ℕ} (p q : Fin n) (letter : PauliLetter)
    (hl : letter = .x ∨ letter = .y) :
    (hoppingString p q letter).weight = Nat.dist p.val q.val + 1 := by
  rw [PauliString.weight, hoppingString_support p q letter hl, Fin.card_Icc]
  simp only [Fin.coe_max, Fin.coe_min, Nat.dist]
  omega

/-- Exactly the two endpoints carry the X/Y endpoint letter. -/
lemma hoppingString_endpoint_set {n : ℕ} (p q : Fin n) (letter : PauliLetter)
    (hl : letter = .x ∨ letter = .y) :
    Finset.univ.filter (fun j => hoppingString p q letter j = letter) = {p, q} := by
  ext j
  simp only [Finset.mem_filter_univ, Finset.mem_insert, Finset.mem_singleton]
  rcases hl with rfl | rfl <;> simp only [hoppingString] <;>
    split_ifs <;> simp_all

/-- A distinct bond has exactly two occurrences of its endpoint letter. -/
lemma hoppingString_endpoint_count {n : ℕ} (p q : Fin n) (hpq : p ≠ q)
    (letter : PauliLetter) (hl : letter = .x ∨ letter = .y) :
    (Finset.univ.filter (fun j => hoppingString p q letter j = letter)).card = 2 := by
  rw [hoppingString_endpoint_set p q letter hl]
  simp [hpq]

/-- No other X/Y letter occurs in the string. -/
lemma hoppingString_other_count {n : ℕ} (p q : Fin n) (letter other : PauliLetter)
    (hl : letter = .x ∨ letter = .y) (ho : other = .x ∨ other = .y)
    (hne : letter ≠ other) :
    (Finset.univ.filter (fun j => hoppingString p q letter j = other)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j
  simp only [Finset.mem_filter_univ]
  rcases hl with rfl | rfl <;> rcases ho with rfl | rfl <;>
    simp_all only [ne_eq, not_true_eq_false, hoppingString] <;>
    split_ifs <;> simp_all

end QuantumAlg.JordanWigner
