/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.Native
import all QuantumAlg.Primitives.Trotter.Native
public import QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.Pauli.String
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Util.FinPow

/-!
# Tensor layers for Pauli rotations

The tensor order is the most-significant-wire-first Pauli convention
[WBA11, h2.arxiv2.tex:329]. Every local circuit retains its native leaves.
-/

namespace QuantumAlg.Trotter.PauliRotation

noncomputable section

/-- Split the leading qubit from the remaining computational register. -/
def pair (n : ℕ) : Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  (prodEquiv (m := 1) (n := n)).trans
    (finCongr (congrArg (2 ^ ·) (Nat.add_comm 1 n)))

/-- Value on one most-significant-first wire. -/
def bit {n : ℕ} (x : Fin (2 ^ n)) (j : Fin n) : Bool :=
  x.val.testBit (WireAddress.bitIndex j).val

/-- The same local value as a one-qubit computational label. -/
def digit {n : ℕ} (x : Fin (2 ^ n)) (j : Fin n) : Fin 2 :=
  if bit x j then 1 else 0

lemma bit_pair_zero (n : ℕ) (a : Fin 2) (b : Fin (2 ^ n)) :
    bit (pair n (a, b)) 0 = a.val.testBit 0 := by
  change (prodEquiv (m := 1) (n := n) (a, b)).val.testBit _ = _
  have h : (WireAddress.bitIndex (0 : Fin (n + 1))).val = n + 0 := by
    simp [WireAddress.bitIndex]
  rw [h]
  exact prodEquiv_testBit_left a b (0 : Fin 1)

lemma bit_pair_succ (n : ℕ) (a : Fin 2) (b : Fin (2 ^ n)) (j : Fin n) :
    bit (pair n (a, b)) j.succ = bit b j := by
  change (prodEquiv (m := 1) (n := n) (a, b)).val.testBit _ = _
  have h : (WireAddress.bitIndex j.succ).val = (WireAddress.bitIndex j).val := by
    simp only [WireAddress.bitIndex, Fin.val_succ]
    omega
  rw [h]
  exact prodEquiv_testBit_right (m := 1) a b (WireAddress.bitIndex j)

@[simp] lemma digit_pair_zero (n : ℕ) (a : Fin 2) (b : Fin (2 ^ n)) :
    digit (pair n (a, b)) 0 = a := by
  rw [digit, bit_pair_zero]
  fin_cases a <;> rfl

@[simp] lemma digit_pair_succ (n : ℕ) (a : Fin 2) (b : Fin (2 ^ n)) (j : Fin n) :
    digit (pair n (a, b)) j.succ = digit b j := by
  simp [digit, bit_pair_succ]

lemma digit_injective {n : ℕ} : Function.Injective (digit (n := n)) := by
  induction n with
  | zero => intro x y _; exact @Subsingleton.elim (Fin 1) _ x y
  | succ n ih =>
    intro x y h
    obtain ⟨⟨a, b⟩, rfl⟩ := (pair n).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (pair n).surjective y
    have ha := congrFun h 0
    have hb : digit b = digit d := by
      funext j
      simpa using congrFun h j.succ
    simp only [digit_pair_zero] at ha
    rw [ha, ih hb]

/-- A certified tensor operator in the same order as a Pauli string. -/
def tensorOp : {n : ℕ} → (Fin n → UnitaryOperator (Qubits 1)) →
    UnitaryOperator (Qubits n)
  | 0, _ => 1
  | n + 1, f => UnitaryOperator.reindex (pair n)
      (UnitaryOperator.prodTensor (f 0) (tensorOp fun j => f j.succ))

lemma tensorOp_pair {n : ℕ} (f : Fin (n + 1) → UnitaryOperator (Qubits 1))
    (a c : Fin 2) (b d : Fin (2 ^ n)) :
    tensorOp f (pair n (a, b)) (pair n (c, d)) =
      f 0 a c * tensorOp (fun j => f j.succ) b d := by
  change UnitaryOperator.prodTensor (f 0) (tensorOp fun j => f j.succ)
    ((pair n).symm (pair n (a, b))) ((pair n).symm (pair n (c, d))) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

lemma tensorOp_apply {n : ℕ} (f : Fin n → UnitaryOperator (Qubits 1))
    (x y : Fin (2 ^ n)) :
    tensorOp f x y = ∏ j, f j (digit x j) (digit y j) := by
  induction n with
  | zero =>
    have h : x = y := @Subsingleton.elim (Fin 1) _ x y
    simp [tensorOp, h]
  | succ n ih =>
    obtain ⟨⟨a, b⟩, rfl⟩ := (pair n).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (pair n).surjective y
    rw [tensorOp_pair, ih, Fin.prod_univ_succ]
    simp

lemma tensorOp_pauli {n : ℕ} (P : PauliString n) :
    tensorOp (fun j => (P j).op) = P.op := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Subtype.ext
    ext x y
    obtain ⟨⟨a, b⟩, rfl⟩ := (pair n).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (pair n).surjective y
    rw [tensorOp_pair, ih, PauliString.op_succ_apply]
    have hcast (a : Fin 2) (b : Fin (2 ^ n)) :
        Fin.cast (congrArg (2 ^ ·) (Nat.add_comm n 1)) (pair n (a, b)) =
          prodEquiv (a, b) := by
      apply Fin.ext
      rfl
    rw [hcast, hcast, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- A parallel tensor of actual native one-qubit words on disjoint physical wires. -/
def tensorCircuit : {n : ℕ} → (Fin n → NativeCircuit 1) → NativeCircuit n
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout 0)
  | n + 1, f =>
      (UnitaryCircuit.parallelBinary (f 0) (tensorCircuit fun j => f j.succ)).castQubitWidth
        (Nat.add_comm 1 n)

lemma tensorCircuit_matrix {n : ℕ} (f : Fin n → NativeCircuit 1) :
    (tensorCircuit f).binaryOperator = tensorOp (fun j => (f j).binaryOperator) := by
  induction n with
  | zero => exact NativeCircuit.binaryOperator_identity 0
  | succ n ih =>
    unfold tensorCircuit NativeCircuit.binaryOperator
    rw [UnitaryCircuit.castQubitWidth_binaryMatrix,
      UnitaryCircuit.parallelBinary_binaryMatrix]
    change UnitaryOperator.reindex _ ((f 0).binaryOperator.tensor
      (tensorCircuit (fun j => f j.succ)).binaryOperator) = _
    rw [ih]
    apply Subtype.ext
    rfl

lemma tensorCircuit_eventCost {n : ℕ} (f : Fin n → NativeCircuit 1) :
    (tensorCircuit f).eventCost = ∑ j, (f j).eventCost := by
  induction n with
  | zero => simp [tensorCircuit]
  | succ n ih =>
    rw [tensorCircuit, UnitaryCircuit.castQubitWidth_eventCost,
      UnitaryCircuit.parallelBinary_eventCost, ih, Fin.sum_univ_succ]


lemma tensorOp_mul {n : ℕ} (f g : Fin n → UnitaryOperator (Qubits 1)) :
    tensorOp (fun j => f j * g j) = tensorOp f * tensorOp g := by
  induction n with
  | zero => simp [tensorOp]
  | succ n ih =>
    apply Subtype.ext
    ext x y
    obtain ⟨⟨a, b⟩, rfl⟩ := (pair n).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (pair n).surjective y
    rw [tensorOp_pair, ih]
    change ((f 0 : HilbertOperator (Qubits 1)) * g 0) a c *
      ((tensorOp (fun j => f j.succ) : HilbertOperator (Qubits n)) *
        tensorOp (fun j => g j.succ)) b d = _
    simp only [Matrix.UnitaryGroup.mul_val, Matrix.mul_apply]
    rw [← Equiv.sum_comp (pair n), Fintype.sum_prod_type]
    simp only [tensorOp_pair]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma tensorOp_one (n : ℕ) :
    tensorOp (fun _ : Fin n => (1 : UnitaryOperator (Qubits 1))) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Subtype.ext
    ext x y
    obtain ⟨⟨a, b⟩, rfl⟩ := (pair n).surjective x
    obtain ⟨⟨c, d⟩, rfl⟩ := (pair n).surjective y
    rw [tensorOp_pair, ih]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) a c *
      (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) b d =
      (1 : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ) _ _
    by_cases ha : a = c <;> by_cases hb : b = d <;> simp [Matrix.one_apply, ha, hb]

lemma tensorOp_diagonal {n : ℕ} (f : Fin n → UnitaryOperator (Qubits 1))
    (v : Fin n → Fin 2 → ℂ)
    (hv : ∀ j, (f j : HilbertOperator (Qubits 1)) = Matrix.diagonal (v j)) :
    (tensorOp f : HilbertOperator (Qubits n)) =
      Matrix.diagonal (fun x => ∏ j, v j (digit x j)) := by
  ext x y
  rw [tensorOp_apply]
  simp only [hv]
  by_cases hxy : x = y
  · subst y
    simp
  · have hd : ∃ j, digit x j ≠ digit y j := by
      by_contra! h
      exact hxy (digit_injective (funext h))
    obtain ⟨j, hj⟩ := hd
    rw [Matrix.diagonal_apply_ne _ hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

end
end QuantumAlg.Trotter.PauliRotation
