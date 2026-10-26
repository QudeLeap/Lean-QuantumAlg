/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.JordanWigner.Majoranas
import all QuantumAlg.Components.Pauli.JordanWigner.Majoranas
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Core.Base.Hamiltonian
import Mathlib.Tactic

/-!
# Fermionic ladder operators and occupations

The local ladder signs follow [WBA11, h2.arxiv2.tex:346]. Their raw operator
carrier reflects that creation and annihilation are not unitary.
-/

public section
namespace QuantumAlg.JordanWigner
noncomputable section

/-- Fermionic annihilation, with a Z prefix and vacuum |0...0⟩. -/
@[expose] def annihilation {n : ℕ} (p : Fin n) : HilbertOperator (Qubits n) :=
  (1 / 2 : ℂ) • ((majorana p .x : HilbertOperator (Qubits n)) +
    Complex.I • (majorana p .y : HilbertOperator (Qubits n)))

/-- Fermionic creation, the adjoint ladder operator. -/
@[expose] def creation {n : ℕ} (p : Fin n) : HilbertOperator (Qubits n) :=
  (1 / 2 : ℂ) • ((majorana p .x : HilbertOperator (Qubits n)) -
    Complex.I • (majorana p .y : HilbertOperator (Qubits n)))

/-- Creation is the Hilbert adjoint of annihilation. -/
lemma creation_eq_adjoint {n : ℕ} (p : Fin n) :
    creation p = (annihilation p).conjTranspose := by
  simp only [creation, annihilation, Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
  rw [show (majorana p .x : HilbertOperator (Qubits n)).conjTranspose = _ from
    (majoranaString p .x).op_isHermitian,
    show (majorana p .y : HilbertOperator (Qubits n)).conjTranspose = _ from
    (majoranaString p .y).op_isHermitian]
  simp [sub_eq_add_neg, majorana]

/-- Occupation of one fermionic mode, as a certified Hermitian operator. -/
@[expose] def number {n : ℕ} (p : Fin n) : Hamiltonian (Qubits n) :=
  ⟨(1 / 2 : ℂ) • (1 - ((modeZ p).op : HilbertOperator (Qubits n))),
    (Matrix.isHermitian_one.sub (modeZ p).op_isHermitian).smul (by
      simp [IsSelfAdjoint])⟩

/-- Total fermion number. -/
@[expose] def totalNumber (n : ℕ) : Hamiltonian (Qubits n) :=
  Hamiltonian.sum (fun p : Fin n => number p)

/-- The exact number-operator formula a†a = (I-Z)/2. -/
lemma creation_mul_annihilation {n : ℕ} (p : Fin n) :
    creation p * annihilation p = (number p : HilbertOperator (Qubits n)) := by
  simp only [creation, annihilation, number,
    smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add]
  have hyx := congrArg Neg.neg (majorana_xy_anticommute p).symm
  simp only [neg_neg] at hyx
  rw [majorana_square, majorana_square, hyx, majorana_xy_product]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- The same-mode mixed canonical anticommutation relation. -/
lemma annihilation_creation_car_same {n : ℕ} (p : Fin n) :
    annihilation p * creation p + creation p * annihilation p = 1 := by
  simp only [creation, annihilation, smul_mul_assoc, mul_smul_comm, smul_smul,
    sub_mul, mul_add, add_mul, mul_sub]
  rw [majorana_square, majorana_square]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Two annihilations of the same mode vanish. -/
lemma annihilation_square_zero {n : ℕ} (p : Fin n) :
    annihilation p * annihilation p = 0 := by
  simp only [annihilation, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul]
  rw [majorana_square, majorana_square, majorana_xy_anticommute]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.zero_apply,
    smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- Distinct annihilation operators anticommute. -/
lemma annihilation_anticommute_ne {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    annihilation p * annihilation q = -(annihilation q * annihilation p) := by
  simp only [annihilation, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_add, add_mul]
  rw [majorana_anticommute_ne p q hpq .x .x (Or.inl rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .x .y (Or.inl rfl) (Or.inr rfl),
    majorana_anticommute_ne p q hpq .y .x (Or.inr rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .y .y (Or.inr rfl) (Or.inr rfl)]
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Distinct creation operators anticommute. -/
lemma creation_anticommute_ne {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    creation p * creation q = -(creation q * creation p) := by
  simp only [creation, smul_mul_assoc, mul_smul_comm, smul_smul,
    sub_mul, mul_sub]
  rw [majorana_anticommute_ne p q hpq .x .x (Or.inl rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .x .y (Or.inl rfl) (Or.inr rfl),
    majorana_anticommute_ne p q hpq .y .x (Or.inr rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .y .y (Or.inr rfl) (Or.inr rfl)]
  ext i j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Distinct mixed ladder operators anticommute. -/
lemma annihilation_creation_anticommute_ne {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    annihilation p * creation q = -(creation q * annihilation p) := by
  simp only [annihilation, creation, smul_mul_assoc, mul_smul_comm, smul_smul,
    mul_add, add_mul, sub_mul, mul_sub]
  rw [majorana_anticommute_ne p q hpq .x .x (Or.inl rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .x .y (Or.inl rfl) (Or.inr rfl),
    majorana_anticommute_ne p q hpq .y .x (Or.inr rfl) (Or.inl rfl),
    majorana_anticommute_ne p q hpq .y .y (Or.inr rfl) (Or.inr rfl)]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The mixed canonical anticommutation relation on all modes. -/
lemma annihilation_creation_car {n : ℕ} (p q : Fin n) :
    annihilation p * creation q + creation q * annihilation p =
      if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst q
    simpa using annihilation_creation_car_same p
  · simp [h, annihilation_creation_anticommute_ne p q h]

/-- The annihilation canonical anticommutation relation on all modes. -/
lemma annihilation_car {n : ℕ} (p q : Fin n) :
    annihilation p * annihilation q + annihilation q * annihilation p = 0 := by
  by_cases h : p = q
  · subst q
    simp [annihilation_square_zero p]
  · simp [annihilation_anticommute_ne p q h]

/-- The creation canonical anticommutation relation on all modes. -/
lemma creation_car {n : ℕ} (p q : Fin n) :
    creation p * creation q + creation q * creation p = 0 := by
  have h := congrArg Matrix.conjTranspose (annihilation_car q p)
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_zero, ← creation_eq_adjoint p, ← creation_eq_adjoint q] using h

end
end QuantumAlg.JordanWigner
