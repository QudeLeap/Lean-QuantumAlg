/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Pauli.Letter
public import QuantumAlg.Core.Base.Hamiltonian
public import QuantumAlg.Util.FinPow
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
import Mathlib.Algebra.Ring.Parity

/-!
# Tensor products of Pauli letters

Position zero is the leftmost, most-significant tensor factor. The empty string
is the identity on the one-dimensional empty register. The matrices and tensor
strings follow [WBA11, h2.arxiv2.tex:307] and [WBA11, h2.arxiv2.tex:329].
-/

public section

namespace QuantumAlg

/-- An ordered, phase-free Pauli string on `n` qubits. -/
abbrev PauliString (n : ℕ) := Fin n → PauliLetter

namespace PauliString

/-- Positions occupied by nonidentity letters. -/
@[expose] def support {n : ℕ} (P : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter fun j => P j ≠ .i

/-- Number of nonidentity positions. -/
@[expose] def weight {n : ℕ} (P : PauliString n) : ℕ := P.support.card

/-- Pointwise multiplication with phases discarded. -/
@[expose] def mul {n : ℕ} (P Q : PauliString n) : PauliString n :=
  fun j => PauliLetter.mulLetter (P j) (Q j)

/-- Product of the ordered local phases. -/
@[expose] noncomputable def mulPhase {n : ℕ} (P Q : PauliString n) : ℂ :=
  ∏ j, PauliLetter.mulPhase (P j) (Q j)

private def widthEquiv (n : ℕ) : Fin (2 ^ (1 + n)) ≃ Fin (2 ^ (n + 1)) :=
  finCongr (congrArg (2 ^ ·) (Nat.add_comm 1 n))

/-- Certified tensor product, with the head letter on the most-significant qubit. -/
noncomputable def op : {n : ℕ} → PauliString n → UnitaryOperator (Qubits n)
  | 0, _ => 1
  | n + 1, P => by
    let U := (P 0).op.tensor (op (fun j => P j.succ))
    exact UnitaryOperator.ofMatrix
      (Matrix.reindex (widthEquiv n) (widthEquiv n)
        (U : HilbertOperator (Qubits (1 + n)))) (by
      have hU := Matrix.mem_unitaryGroup_iff.mp U.property
      rw [Matrix.star_eq_conjTranspose] at hU
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv])

/-- The empty Pauli string acts as identity. -/
lemma op_zero (P : PauliString 0) : P.op = 1 := by rfl

private lemma op_succ_raw {n : ℕ} (P : PauliString (n + 1)) :
    (P.op : HilbertOperator (Qubits (n + 1))) =
      Matrix.reindex (widthEquiv n) (widthEquiv n)
        (HilbertOperator.tensor ((P 0).op : HilbertOperator (Qubits 1))
          ((op fun j => P j.succ) : HilbertOperator (Qubits n))) := rfl

/-- Recursive entries make the most-significant head factor explicit. -/
lemma op_succ_apply {n : ℕ} (P : PauliString (n + 1))
    (j k : Fin (2 ^ (n + 1))) :
    P.op j k =
      (P 0).op
        (prodEquiv.symm (Fin.cast (congrArg (2 ^ ·) (Nat.add_comm n 1)) j)).1
        (prodEquiv.symm (Fin.cast (congrArg (2 ^ ·) (Nat.add_comm n 1)) k)).1 *
      (op fun i => P i.succ)
        (prodEquiv.symm (Fin.cast (congrArg (2 ^ ·) (Nat.add_comm n 1)) j)).2
        (prodEquiv.symm (Fin.cast (congrArg (2 ^ ·) (Nat.add_comm n 1)) k)).2 := by
  rfl

/-- Every Pauli string is Hermitian, including the empty string. -/
lemma op_isHermitian {n : ℕ} (P : PauliString n) :
    (P.op : HilbertOperator (Qubits n)).IsHermitian := by
  induction n with
  | zero => exact Matrix.isHermitian_one
  | succ n ih =>
    change (P.op : HilbertOperator (Qubits (n + 1))).conjTranspose = _
    rw [op_succ_raw, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      HilbertOperator.conjTranspose_tensor, (P 0).letter_op_isHermitian,
      ih (fun j => P j.succ)]

/-- The raw operator view retains the certified unitarity invariant. -/
lemma op_isUnitary {n : ℕ} (P : PauliString n) :
    (P.op : HilbertOperator (Qubits n)) ∈ Matrix.unitaryGroup (Qubits n).Index ℂ :=
  P.op.property

/-- A Pauli string as a Hermitian Hamiltonian. -/
@[expose] noncomputable def hamiltonian {n : ℕ} (P : PauliString n) : Hamiltonian (Qubits n) :=
  ⟨P.op, P.op_isHermitian⟩

@[simp] lemma coe_hamiltonian {n : ℕ} (P : PauliString n) :
    (P.hamiltonian : HilbertOperator (Qubits n)) = P.op := rfl

/-- Multiplication is pointwise letter multiplication times the exact total phase. -/
lemma op_mul_op {n : ℕ} (P Q : PauliString n) :
    (P.op : HilbertOperator (Qubits n)) * (Q.op : HilbertOperator (Qubits n)) =
      mulPhase P Q • ((mul P Q).op : HilbertOperator (Qubits n)) := by
  induction n with
  | zero => simp [op, mulPhase]
  | succ n ih =>
    rw [op_succ_raw, op_succ_raw, op_succ_raw]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [HilbertOperator.tensor_mul_tensor, PauliLetter.letter_op_mul_op, ih]
    simp only [mulPhase, Fin.prod_univ_succ]
    ext i j
    simp only [Matrix.submatrix_apply, HilbertOperator.tensor_apply,
      Matrix.smul_apply, smul_eq_mul]
    have htail : mul (fun j => P j.succ) (fun j => Q j.succ) =
        (fun j => PauliLetter.mulLetter (P j.succ) (Q j.succ)) := rfl
    rw [htail]
    simp only [mul]
    ring

/-- The total multiplication phase has unit modulus. -/
lemma string_mulPhase_norm {n : ℕ} (P Q : PauliString n) : ‖mulPhase P Q‖ = 1 := by
  simp [mulPhase, norm_prod, PauliLetter.mulPhase_norm]

/-- Number of locally anticommuting positions. -/
@[expose] def anticommutingCount {n : ℕ} (P Q : PauliString n) : ℕ :=
  ∑ j, if PauliLetter.anticommutes (P j) (Q j) then 1 else 0

/-- Global commutation is even parity of locally anticommuting positions. -/
@[expose] def Commute {n : ℕ} (P Q : PauliString n) : Prop := Even (anticommutingCount P Q)

/-- Global anticommutation is odd parity of locally anticommuting positions. -/
@[expose] def AntiCommute {n : ℕ} (P Q : PauliString n) : Prop := Odd (anticommutingCount P Q)

instance {n : ℕ} (P Q : PauliString n) : Decidable (Commute P Q) :=
  inferInstanceAs (Decidable (Even (anticommutingCount P Q)))

instance {n : ℕ} (P Q : PauliString n) : Decidable (AntiCommute P Q) :=
  inferInstanceAs (Decidable (Odd (anticommutingCount P Q)))

private lemma string_phase_swap {n : ℕ} (P Q : PauliString n) :
    mulPhase P Q = (-1 : ℂ) ^ anticommutingCount P Q * mulPhase Q P := by
  unfold mulPhase anticommutingCount
  simp only [PauliLetter.letter_phase_swap (P _) (Q _), Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp_all

/-- The matrix swap sign is the parity of all locally anticommuting positions. -/
lemma op_swap_sign {n : ℕ} (P Q : PauliString n) :
    (P.op : HilbertOperator (Qubits n)) * (Q.op : HilbertOperator (Qubits n)) =
      (-1 : ℂ) ^ anticommutingCount P Q •
        ((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n))) := by
  rw [op_mul_op, op_mul_op, string_phase_swap, mul_smul]
  have hm : mul P Q = mul Q P := funext fun j =>
    PauliLetter.mulLetter_comm (P j) (Q j)
  rw [hm]

private lemma unitary_raw_ne_zero {n : ℕ} (U : UnitaryOperator (Qubits n)) :
    (U : HilbertOperator (Qubits n)) ≠ 0 := by
  intro h
  have hU := Matrix.mem_unitaryGroup_iff.mp U.property
  rw [h, zero_mul] at hU
  have hentry := congrArg (fun M : HilbertOperator (Qubits n) =>
    M ⟨0, Nat.two_pow_pos n⟩ ⟨0, Nat.two_pow_pos n⟩) hU
  simp at hentry

/-- The finite parity decision is equivalent to actual matrix commutation. -/
lemma commute_iff_op_commute {n : ℕ} (P Q : PauliString n) :
    Commute P Q ↔ _root_.Commute (P.op : HilbertOperator (Qubits n))
      (Q.op : HilbertOperator (Qubits n)) := by
  rw [Commute, ← neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)]
  constructor
  · intro h
    change (P.op : HilbertOperator (Qubits n)) * (Q.op : HilbertOperator (Qubits n)) = _
    rw [op_swap_sign, h, one_smul]
  · intro h
    apply smul_left_injective ℂ (unitary_raw_ne_zero (Q.op * P.op))
    change (-1 : ℂ) ^ anticommutingCount P Q •
      ((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n))) =
      (1 : ℂ) • ((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n)))
    rw [← op_swap_sign, one_smul, h.eq]

/-- The finite parity decision is equivalent to actual matrix anticommutation. -/
lemma antiCommute_iff_op_anticommute {n : ℕ} (P Q : PauliString n) :
    AntiCommute P Q ↔
      (P.op : HilbertOperator (Qubits n)) * (Q.op : HilbertOperator (Qubits n)) =
        -((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n))) := by
  rw [AntiCommute, ← neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℂ) ≠ 1)]
  constructor
  · intro h
    rw [op_swap_sign, h, neg_one_smul]
  · intro h
    apply smul_left_injective ℂ (unitary_raw_ne_zero (Q.op * P.op))
    change (-1 : ℂ) ^ anticommutingCount P Q •
      ((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n))) =
      (-1 : ℂ) • ((Q.op : HilbertOperator (Qubits n)) * (P.op : HilbertOperator (Qubits n)))
    rw [← op_swap_sign, neg_one_smul, h]

end PauliString
end QuantumAlg
