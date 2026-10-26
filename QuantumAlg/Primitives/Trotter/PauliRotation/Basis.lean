/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.PauliRotation.Parity
import all QuantumAlg.Primitives.Trotter.PauliRotation.Parity
public import QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Pauli.Letter

/-!
# Pauli eigenbasis changes

The basis-change construction [WBA11, h2.arxiv2.tex:402-412] is realized here
with H for X, and S three times then H on input and H then S on output for Y.
This S/H realization retains the exact complex phase and literal S events.
-/

namespace QuantumAlg.Trotter.PauliRotation

noncomputable section

open NormalizedVector

/-- One-qubit identity with its complete physical interface. -/
def idle : NativeCircuit 1 :=
  UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout 1)

/-- Input eigenbasis circuit; inverse S is three actual S gates. -/
def basisIn (a : PauliLetter) : NativeCircuit 1 :=
  match a with
  | .i | .z => idle
  | .x => (NativeCircuit.single Gate.HOp)
  | .y => (UnitaryCircuit.iterate 3 (NativeCircuit.single Gate.SOp)).seq
      (NativeCircuit.single Gate.HOp)

/-- Output eigenbasis circuit. -/
def basisOut (a : PauliLetter) : NativeCircuit 1 :=
  match a with
  | .i | .z => idle
  | .x => (NativeCircuit.single Gate.HOp)
  | .y => (NativeCircuit.single Gate.HOp).seq (NativeCircuit.single Gate.SOp)

/-- Parallel input basis changes on every wire. -/
def inputLayer {n : ℕ} (P : PauliString n) : NativeCircuit n :=
  tensorCircuit (fun j => basisIn (P j))

/-- Parallel output basis changes on every wire. -/
def outputLayer {n : ℕ} (P : PauliString n) : NativeCircuit n :=
  tensorCircuit (fun j => basisOut (P j))

/-- Z on exactly the nonidentity letters. -/
def zString {n : ℕ} (P : PauliString n) : PauliString n :=
  fun j => if P j = .i then .i else .z


private lemma hadamard_mul_self : Gate.HOp * Gate.HOp = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gate.HOp, Matrix.mul_apply, invSqrt2_mul_self] <;> norm_num

lemma basis_inverse (a : PauliLetter) :
    (basisOut a).binaryOperator * (basisIn a).binaryOperator = 1 := by
  simp only [basisOut, basisIn, idle]
  apply Subtype.ext
  cases a with
  | i => simp
  | z => simp
  | x => simpa only [NativeCircuit.binaryOperator_single] using
      congrArg (fun U : UnitaryOperator (Qubits 1) =>
      (U : HilbertOperator (Qubits 1))) hadamard_mul_self
  | y =>
    simp only [NativeCircuit.binaryOperator_seq, NativeCircuit.binaryOperator_single,
      NativeCircuit.binaryOperator_iterate]
    change ((Gate.SOp : HilbertOperator (Qubits 1)) * Gate.HOp) *
      ((Gate.HOp : HilbertOperator (Qubits 1)) * Gate.SOp ^ 3) = 1
    have hH := congrArg (fun U : UnitaryOperator (Qubits 1) =>
      (U : HilbertOperator (Qubits 1))) hadamard_mul_self
    change (Gate.HOp : HilbertOperator (Qubits 1)) * Gate.HOp = 1 at hH
    rw [mul_assoc, ← mul_assoc (Gate.HOp : HilbertOperator (Qubits 1)), hH, one_mul,
      ← pow_succ']
    exact congrArg (fun U : UnitaryOperator (Qubits 1) =>
      (U : HilbertOperator (Qubits 1))) Gate.SOp_pow_four

lemma basis_conjugates (a : PauliLetter) :
    (basisOut a).binaryOperator * (if a = .i then PauliLetter.i.op else PauliLetter.z.op) *
      (basisIn a).binaryOperator = a.op := by
  simp only [basisOut, basisIn, idle]
  apply Subtype.ext
  cases a with
  | i => simp [PauliLetter.op]
  | z => simp [PauliLetter.op]
  | x =>
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [PauliLetter.op, Gate.HOp, Gate.ZOp, Gate.XOp,
        UnitaryOperator.ofPerm, Equiv.Perm.permMatrix, Matrix.mul_apply,
        invSqrt2_mul_self] <;> norm_num
  | y =>
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [PauliLetter.op, Gate.HOp, Gate.SOp, Gate.ZOp,
        Gate.YOp, Matrix.mul_apply, pow_succ, invSqrt2_mul_self] <;>
      ring_nf <;> norm_num [invSqrt2_sq] <;> ring

lemma layers_inverse {n : ℕ} (P : PauliString n) :
    (outputLayer P).binaryOperator * (inputLayer P).binaryOperator = 1 := by
  rw [inputLayer, outputLayer, tensorCircuit_matrix, tensorCircuit_matrix, ← tensorOp_mul]
  simp only [basis_inverse]
  exact tensorOp_one n

lemma layers_conjugates {n : ℕ} (P : PauliString n) :
    (outputLayer P).binaryOperator * (zString P).op * (inputLayer P).binaryOperator = P.op := by
  rw [inputLayer, outputLayer, tensorCircuit_matrix, tensorCircuit_matrix,
    ← tensorOp_pauli, ← tensorOp_mul, ← tensorOp_mul]
  have hlocal (j : Fin n) :
      (basisOut (P j)).binaryOperator * ((zString P) j).op *
        (basisIn (P j)).binaryOperator = (P j).op := by
    simpa only [zString, apply_ite PauliLetter.op] using basis_conjugates (P j)
  simp only [hlocal]
  exact tensorOp_pauli P


lemma zString_diagonal {n : ℕ} (P : PauliString n) :
    ((zString P).op : HilbertOperator (Qubits n)) =
      Matrix.diagonal (fun x => ∏ j ∈ P.support, sign x j) := by
  rw [← tensorOp_pauli]
  have hlocal (j : Fin n) :
      (((zString P) j).op : HilbertOperator (Qubits 1)) =
        Matrix.diagonal (fun a : Fin 2 =>
          if P j = .i then 1 else if a = 1 then (-1 : ℂ) else 1) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      cases hj : P j <;> simp [zString, hj, PauliLetter.op, Gate.ZOp]
  rw [tensorOp_diagonal _ _ hlocal]
  congr 1
  funext x
  rw [PauliString.support, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : P j = .i
  · simp [hj]
  · cases hbit : bit x j <;> simp [sign, digit, hj, hbit]

end
end QuantumAlg.Trotter.PauliRotation
