/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import Mathlib.Tactic

/-!
# The Majorana Clifford relations

Z prefixes implement the canonical anticommutation in the reversed mode order
of [WBA11, h2.arxiv2.tex:329].
-/

public section
namespace QuantumAlg.JordanWigner

/-- The certified X/Y Majorana operator. -/
noncomputable def majorana {n : ℕ} (p : Fin n) (letter : PauliLetter) :
    UnitaryOperator (Qubits n) := (majoranaString p letter).op

/-- Every Majorana Pauli tensor squares to identity. -/
lemma majorana_square {n : ℕ} (p : Fin n) (letter : PauliLetter) :
    (majorana p letter : HilbertOperator (Qubits n)) *
      (majorana p letter : HilbertOperator (Qubits n)) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp (majorana p letter).property
  rw [Matrix.star_eq_conjTranspose,
    show (majorana p letter : HilbertOperator (Qubits n)).conjTranspose =
      (majorana p letter : HilbertOperator (Qubits n)) from
      (majoranaString p letter).op_isHermitian] at h
  exact h

private lemma majorana_count_lt {n : ℕ} (p q : Fin n) (hpq : p < q)
    (a b : PauliLetter) (ha : a = .x ∨ a = .y) (hb : b = .x ∨ b = .y) :
    PauliString.anticommutingCount (majoranaString p a) (majoranaString q b) = 1 := by
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (majoranaString p a j) (majoranaString q b j)
        then 1 else 0 : ℕ) = if j = p then 1 else 0 := by
    intro j
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [majoranaString] <;> split_ifs <;>
      simp_all [PauliLetter.anticommutes] <;> omega
  simp only [PauliString.anticommutingCount, hpoint]
  simp

/-- Different fermionic modes have anticommuting Majoranas of either flavor. -/
lemma majorana_anticommute_ne {n : ℕ} (p q : Fin n) (hpq : p ≠ q)
    (a b : PauliLetter) (ha : a = .x ∨ a = .y) (hb : b = .x ∨ b = .y) :
    (majorana p a : HilbertOperator (Qubits n)) *
      (majorana q b : HilbertOperator (Qubits n)) =
      -((majorana q b : HilbertOperator (Qubits n)) *
        (majorana p a : HilbertOperator (Qubits n))) := by
  rcases lt_or_gt_of_ne hpq with h | h
  · apply (PauliString.antiCommute_iff_op_anticommute _ _).mp
    rw [PauliString.AntiCommute, majorana_count_lt p q h a b ha hb]
    decide
  · have hswap := (PauliString.antiCommute_iff_op_anticommute
      (majoranaString q b) (majoranaString p a)).mp (by
        rw [PauliString.AntiCommute, majorana_count_lt q p h b a hb ha]
        decide)
    simpa [majorana] using congrArg Neg.neg hswap.symm

/-- The two Majoranas of the same mode anticommute. -/
lemma majorana_xy_anticommute {n : ℕ} (p : Fin n) :
    (majorana p .x : HilbertOperator (Qubits n)) *
      (majorana p .y : HilbertOperator (Qubits n)) =
      -((majorana p .y : HilbertOperator (Qubits n)) *
        (majorana p .x : HilbertOperator (Qubits n))) := by
  apply (PauliString.antiCommute_iff_op_anticommute _ _).mp
  have hpoint : ∀ j : Fin n,
      (if PauliLetter.anticommutes (majoranaString p .x j) (majoranaString p .y j)
        then 1 else 0 : ℕ) = if j = p then 1 else 0 := by
    intro j
    simp only [majoranaString]
    split_ifs <;> simp_all [PauliLetter.anticommutes]
  simp only [PauliString.AntiCommute, PauliString.anticommutingCount, hpoint]
  simp

/-- The local Majorana product is exactly i times the mode parity operator. -/
lemma majorana_xy_product {n : ℕ} (p : Fin n) :
    (majorana p .x : HilbertOperator (Qubits n)) *
      (majorana p .y : HilbertOperator (Qubits n)) =
      Complex.I • ((modeZ p).op : HilbertOperator (Qubits n)) := by
  have hletters : PauliString.mul (majoranaString p .x) (majoranaString p .y) =
      modeZ p := by
    funext j
    simp only [PauliString.mul, majoranaString, modeZ]
    split_ifs <;> rfl
  have hphase : PauliString.mulPhase (majoranaString p .x) (majoranaString p .y) =
      Complex.I := by
    unfold PauliString.mulPhase
    rw [Finset.prod_eq_single p]
    · simp [majoranaString, PauliLetter.mulPhase]
    · intro j _ hj
      simp only [majoranaString, if_neg hj]
      split_ifs <;> rfl
    · simp
  exact (PauliString.op_mul_op _ _).trans (by rw [hphase, hletters])

end QuantumAlg.JordanWigner
