/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.JordanWigner.Ladders
public import QuantumAlg.Components.Pauli.JordanWigner.Commutation
import all QuantumAlg.Components.Pauli.JordanWigner.Ladders
import all QuantumAlg.Components.Pauli.JordanWigner.Majoranas
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Core.Base.Hamiltonian
import Mathlib.Tactic

/-!
# Complete fermionic hopping bonds

The hopping formula is the Jordan–Wigner image of the number-excitation term
in [WBA11, h2.arxiv2.tex:922]. Both endpoint flavors are retained.
-/

public section
namespace QuantumAlg.JordanWigner
noncomputable section

/-- The Hermitian complete hopping bond, containing both endpoint flavors. -/
@[expose] def hopping {n : ℕ} (p q : Fin n) : Hamiltonian (Qubits n) :=
  ⟨(1 / 2 : ℂ) • (((hoppingString p q .x).op : HilbertOperator (Qubits n)) +
    ((hoppingString p q .y).op : HilbertOperator (Qubits n))),
    ((hoppingString p q .x).op_isHermitian.add
      (hoppingString p q .y).op_isHermitian).smul (by simp [IsSelfAdjoint])⟩

/-- Reversing a complete hopping bond leaves it unchanged. -/
lemma hopping_symm {n : ℕ} (p q : Fin n) : hopping p q = hopping q p := by
  simp only [hopping, hoppingString_symm p q]

private lemma majorana_xy_lt {n : ℕ} (p q : Fin n) (hpq : p < q) :
    (majorana p .x : HilbertOperator (Qubits n)) *
      (majorana q .y : HilbertOperator (Qubits n)) =
      (-Complex.I) • ((hoppingString p q .y).op : HilbertOperator (Qubits n)) := by
  have hletters : PauliString.mul (majoranaString p .x) (majoranaString q .y) =
      hoppingString p q .y := by
    funext j
    simp only [PauliString.mul, majoranaString, hoppingString,
      min_eq_left (le_of_lt hpq), max_eq_right (le_of_lt hpq)]
    split_ifs <;> simp_all [PauliLetter.mulLetter] <;> omega
  have hphase : PauliString.mulPhase (majoranaString p .x) (majoranaString q .y) =
      -Complex.I := by
    unfold PauliString.mulPhase
    rw [Finset.prod_eq_single p]
    · simp [majoranaString, ne_of_lt hpq, hpq, PauliLetter.mulPhase]
    · intro j _ hj
      simp only [majoranaString, if_neg hj]
      split_ifs <;> simp_all [PauliLetter.mulPhase]
      omega
    · simp
  exact (PauliString.op_mul_op _ _).trans (by rw [hphase, hletters])

private lemma majorana_yx_lt {n : ℕ} (p q : Fin n) (hpq : p < q) :
    (majorana p .y : HilbertOperator (Qubits n)) *
      (majorana q .x : HilbertOperator (Qubits n)) =
      (Complex.I) • ((hoppingString p q .x).op : HilbertOperator (Qubits n)) := by
  have hletters : PauliString.mul (majoranaString p .y) (majoranaString q .x) =
      hoppingString p q .x := by
    funext j
    simp only [PauliString.mul, majoranaString, hoppingString,
      min_eq_left (le_of_lt hpq), max_eq_right (le_of_lt hpq)]
    split_ifs <;> simp_all [PauliLetter.mulLetter] <;> omega
  have hphase : PauliString.mulPhase (majoranaString p .y) (majoranaString q .x) =
      Complex.I := by
    unfold PauliString.mulPhase
    rw [Finset.prod_eq_single p]
    · simp [majoranaString, ne_of_lt hpq, hpq, PauliLetter.mulPhase]
    · intro j _ hj
      simp only [majoranaString, if_neg hj]
      split_ifs <;> simp_all [PauliLetter.mulPhase]
      omega
    · simp
  exact (PauliString.op_mul_op _ _).trans (by rw [hphase, hletters])

private lemma hopping_ladder_lt {n : ℕ} (p q : Fin n) (hpq : p < q) :
    creation p * annihilation q + creation q * annihilation p =
      (hopping p q : HilbertOperator (Qubits n)) := by
  simp only [creation, annihilation, hopping, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_add, sub_mul]
  rw [majorana_anticommute_ne q p (ne_of_gt hpq) .x .x (Or.inl rfl) (Or.inl rfl),
    majorana_anticommute_ne q p (ne_of_gt hpq) .x .y (Or.inl rfl) (Or.inr rfl),
    majorana_anticommute_ne q p (ne_of_gt hpq) .y .x (Or.inr rfl) (Or.inl rfl),
    majorana_anticommute_ne q p (ne_of_gt hpq) .y .y (Or.inr rfl) (Or.inr rfl),
    majorana_xy_lt p q hpq, majorana_yx_lt p q hpq]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The complete Pauli bond is exactly a†p aq + a†q ap for distinct modes. -/
lemma hopping_eq_ladders {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    (hopping p q : HilbertOperator (Qubits n)) =
      creation p * annihilation q + creation q * annihilation p := by
  rcases lt_or_gt_of_ne hpq with h | h
  · exact (hopping_ladder_lt p q h).symm
  · rw [hopping_symm p q, ← hopping_ladder_lt q p h, add_comm]

end
end QuantumAlg.JordanWigner
