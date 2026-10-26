/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Components.Pauli.JordanWigner.Hopping
import all QuantumAlg.Components.Pauli.JordanWigner.Ladders
import all QuantumAlg.Components.Pauli.JordanWigner.Strings
import all QuantumAlg.Core.Base.Hamiltonian
import Mathlib.Tactic

/-!
# Number-conserving bilinear algebra

The bilinear commutator and four-cycle matching identity are elementary
consequences of the canonical anticommutation relations.
-/

public section
namespace QuantumAlg.JordanWigner
noncomputable section

/-- The number-conserving fermionic bilinear a†p aq. -/
@[expose] def bilinear {n : ℕ} (p q : Fin n) : HilbertOperator (Qubits n) :=
  creation p * annihilation q

private lemma bilinear_product_expand {n : ℕ} (p q r s : Fin n) :
    bilinear p q * bilinear r s +
      (creation p * creation r) * (annihilation q * annihilation s) =
      if q = r then bilinear p s else 0 := by
  calc
    _ = creation p * (annihilation q * creation r + creation r * annihilation q) *
        annihilation s := by simp only [bilinear]; noncomm_ring
    _ = _ := by rw [annihilation_creation_car q r]; split_ifs <;> simp [bilinear]

/-- The exact commutator algebra of all fermionic bilinears. -/
lemma bilinear_commutator {n : ℕ} (p q r s : Fin n) :
    bilinear p q * bilinear r s - bilinear r s * bilinear p q =
      (if q = r then bilinear p s else 0) - (if s = p then bilinear r q else 0) := by
  have hcc : creation p * creation r = -(creation r * creation p) :=
    eq_neg_of_add_eq_zero_left (creation_car p r)
  have haa : annihilation q * annihilation s = -(annihilation s * annihilation q) :=
    eq_neg_of_add_eq_zero_left (annihilation_car q s)
  have hquartic : (creation p * creation r) * (annihilation q * annihilation s) =
      (creation r * creation p) * (annihilation s * annihilation q) := by
    rw [hcc, haa, neg_mul_neg]
  have h₁ := bilinear_product_expand p q r s
  have h₂ := bilinear_product_expand r s p q
  rw [← hquartic] at h₂
  linear_combination (norm := noncomm_ring) h₁ - h₂

private def comm {n : ℕ} (A B : HilbertOperator (Qubits n)) := A * B - B * A

private lemma comm_add_left {n : ℕ} (A B C : HilbertOperator (Qubits n)) :
    comm (A + B) C = comm A C + comm B C := by unfold comm; noncomm_ring

private lemma comm_add_right {n : ℕ} (A B C : HilbertOperator (Qubits n)) :
    comm A (B + C) = comm A B + comm A C := by unfold comm; noncomm_ring

private lemma comm_bilinear {n : ℕ} (p q r s : Fin n) :
    comm (bilinear p q) (bilinear r s) =
      (if q = r then bilinear p s else 0) - (if s = p then bilinear r q else 0) :=
  bilinear_commutator p q r s

/-- Disjoint complete hopping bonds commute. -/
lemma hopping_commute_disjoint {n : ℕ} (p q r s : Fin n)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    Commute (hopping p q : HilbertOperator (Qubits n))
      (hopping r s : HilbertOperator (Qubits n)) := by
  apply sub_eq_zero.mp
  change comm (hopping p q : HilbertOperator (Qubits n))
    (hopping r s : HilbertOperator (Qubits n)) = 0
  rw [hopping_eq_ladders p q hpq, hopping_eq_ladders r s hrs]
  change comm (bilinear p q + bilinear q p) (bilinear r s + bilinear s r) = 0
  simp only [comm_add_left, comm_add_right, comm_bilinear]
  simp [hpr, hps, hqr, hqs, Ne.symm hpr, Ne.symm hps, Ne.symm hqr, Ne.symm hqs]

/-- On four distinct cyclic modes the two opposite-edge matchings commute.
This identity allows arbitrary mode ordering and gaps. -/
lemma hopping_four_cycle_commute {n : ℕ} (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Commute ((hopping a b : HilbertOperator (Qubits n)) +
      (hopping c d : HilbertOperator (Qubits n)))
      ((hopping b c : HilbertOperator (Qubits n)) +
        (hopping d a : HilbertOperator (Qubits n))) := by
  apply sub_eq_zero.mp
  change comm ((hopping a b : HilbertOperator (Qubits n)) +
      (hopping c d : HilbertOperator (Qubits n)))
    ((hopping b c : HilbertOperator (Qubits n)) +
      (hopping d a : HilbertOperator (Qubits n))) = 0
  rw [hopping_eq_ladders a b hab, hopping_eq_ladders c d hcd,
    hopping_eq_ladders b c hbc, hopping_eq_ladders d a had.symm]
  change comm ((bilinear a b + bilinear b a) + (bilinear c d + bilinear d c))
    ((bilinear b c + bilinear c b) + (bilinear d a + bilinear a d)) = 0
  simp only [comm_add_left, comm_add_right, comm_bilinear]
  simp [hab, hac, had, hbc, hbd, hcd,
    Ne.symm hab, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, Ne.symm hcd]
  abel

private lemma comm_sum_left {n : ℕ} {ι : Type*} (S : Finset ι)
    (A : ι → HilbertOperator (Qubits n)) (B : HilbertOperator (Qubits n)) :
    comm (∑ j ∈ S, A j) B = ∑ j ∈ S, comm (A j) B := by
  simp only [comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

/-- The occupation operator is the diagonal fermionic bilinear. -/
lemma number_eq_bilinear {n : ℕ} (p : Fin n) :
    (number p : HilbertOperator (Qubits n)) = bilinear p p :=
  (creation_mul_annihilation p).symm

/-- Total particle number commutes with every number-conserving bilinear. -/
lemma totalNumber_commute_bilinear {n : ℕ} (p q : Fin n) :
    Commute (totalNumber n : HilbertOperator (Qubits n)) (bilinear p q) := by
  apply sub_eq_zero.mp
  change comm (∑ r : Fin n, (number r : HilbertOperator (Qubits n))) (bilinear p q) = 0
  have hn : ∀ r : Fin n, (number r : HilbertOperator (Qubits n)) = bilinear r r :=
    fun r => number_eq_bilinear r
  simp only [hn, comm_sum_left, comm_bilinear]
  simp [Finset.sum_sub_distrib]

/-- Total particle number is conserved by each complete hopping bond. -/
lemma totalNumber_commute_hopping {n : ℕ} (p q : Fin n) (hpq : p ≠ q) :
    Commute (totalNumber n : HilbertOperator (Qubits n))
      (hopping p q : HilbertOperator (Qubits n)) := by
  rw [hopping_eq_ladders p q hpq]
  exact (totalNumber_commute_bilinear p q).add_right (totalNumber_commute_bilinear q p)

/-- Mode parity is identity minus twice the mode occupation. -/
lemma modeZ_eq_one_sub_number {n : ℕ} (p : Fin n) :
    ((modeZ p).op : HilbertOperator (Qubits n)) =
      1 - (2 : ℂ) • (number p : HilbertOperator (Qubits n)) := by
  simp only [number]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Every mode parity commutes with total fermion number. -/
lemma totalNumber_commute_modeZ {n : ℕ} (p : Fin n) :
    Commute (totalNumber n : HilbertOperator (Qubits n))
      ((modeZ p).op : HilbertOperator (Qubits n)) := by
  rw [modeZ_eq_one_sub_number p, number_eq_bilinear p]
  change (totalNumber n : HilbertOperator (Qubits n)) * (1 - (2 : ℂ) • bilinear p p) =
    (1 - (2 : ℂ) • bilinear p p) * (totalNumber n : HilbertOperator (Qubits n))
  simp only [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  rw [(totalNumber_commute_bilinear p p).eq]

end
end QuantumAlg.JordanWigner
