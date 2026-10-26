/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.Trotter.PauliRotation.Basis
import all QuantumAlg.Primitives.Trotter.PauliRotation.Basis
import all QuantumAlg.Primitives.Trotter.PauliRotation.Parity
import all QuantumAlg.Primitives.Trotter.PauliRotation.Tensor
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Oracle.TimeEvolution
import all QuantumAlg.Components.Oracle.TimeEvolution
import all QuantumAlg.Util.Matrix.ExpInvolution

/-!
# Exact central rotation and parity conjugation

The repository rotation convention uses `rotZ (-θ)` for
`exp (-i θ Z)`, equivalent to the standard `Rz (2 θ)` convention
[WBA11, h2.arxiv2.tex:384-399]. The operator proof retains the scalar phase.
-/

namespace QuantumAlg.Trotter.PauliRotation

noncomputable section

/-- Identity coefficient in the involution exponential. -/
def cosine (θ : ℝ) : ℂ := Complex.cosh (-(Complex.I * (θ : ℂ)))

/-- Pauli coefficient in the involution exponential. -/
def sine (θ : ℝ) : ℂ := Complex.sinh (-(Complex.I * (θ : ℂ)))

/-- One actual Z rotation placed on the selected support target. -/
def rotationAt {n : ℕ} (t : Fin n) (θ : ℝ) : NativeCircuit n :=
  tensorCircuit (fun j => if j = t then NativeCircuit.single (rotZOp (-θ)) else idle)

lemma rotationAt_matrix {n : ℕ} (t : Fin n) (θ : ℝ) :
    ((rotationAt t θ).binaryOperator : HilbertOperator (Qubits n)) =
      cosine θ • 1 + sine θ • Matrix.diagonal (fun x => sign x t) := by
  rw [rotationAt, tensorCircuit_matrix]
  simp only [apply_ite]
  have hlocal (j : Fin n) :
      (((if j = t then (NativeCircuit.single (rotZOp (-θ))).binaryOperator
        else idle.binaryOperator) :
        UnitaryOperator (Qubits 1)) : HilbertOperator (Qubits 1)) =
      Matrix.diagonal (fun a : Fin 2 => if j = t then
        cosine θ + sine θ * (if a = 1 then -1 else 1) else 1) := by
    by_cases hj : j = t
    · simp only [hj, if_true]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [NativeCircuit.binaryOperator_single, rotZOp, cosine, sine, Complex.cosh, Complex.sinh,
          mul_comm] <;> ring
    · simp [hj, idle]
  rw [tensorOp_diagonal _ _ hlocal]
  ext x y
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp only [if_true, mul_one]
    unfold sign digit
    cases bit x t <;> simp
  · simp [hxy]

lemma rotationAt_eventCost {n : ℕ} (t : Fin n) (θ : ℝ) :
    (rotationAt t θ).eventCost = ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) := by
  rw [rotationAt, tensorCircuit_eventCost]
  have localCost (j : Fin n) :
      (if j = t then NativeCircuit.single (rotZOp (-θ)) else idle).eventCost =
        if j = t then ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit) else 0 := by
    by_cases same : j = t <;> simp [same, idle]
  simp_rw [localCost]
  simp


/-- Compute support parity, rotate the selected wire, and uncompute parity. -/
def central {n : ℕ} (P : PauliString n) (t : Fin n) (θ : ℝ) :
    NativeCircuit n :=
  let C := parity t (controls P t)
  C.seq ((rotationAt t θ).seq C.inverse)

lemma central_matrix {n : ℕ} (P : PauliString n) (t : Fin n)
    (ht : t ∈ P.support) (θ : ℝ) :
    ((central P t θ).binaryOperator : HilbertOperator (Qubits n)) =
      cosine θ • 1 + sine θ • ((zString P).op : HilbertOperator (Qubits n)) := by
  let C := (parity t (controls P t)).binaryOperator
  have hunit : ((C⁻¹ : UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) *
      (C : HilbertOperator (Qubits n)) = 1 :=
    congrArg (fun V : UnitaryOperator (Qubits n) =>
      (V : HilbertOperator (Qubits n))) (inv_mul_cancel C)
  simp only [central, NativeCircuit.binaryOperator_seq, NativeCircuit.binaryOperator_inverse]
  change ((C⁻¹ : UnitaryOperator (Qubits n)) : HilbertOperator (Qubits n)) *
    ((rotationAt t θ).binaryOperator : HilbertOperator (Qubits n)) * C = _
  rw [rotationAt_matrix, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, mul_one, hunit]
  have hd : (fun x => sign (parityPerm t (controls P t) x) t) =
      (fun x => ∏ j ∈ P.support, sign x j) := by
    funext x
    rw [sign_parity_target, controls_sign_prod]
    exact Finset.prod_erase_mul P.support (sign x) ht
  rw [parity_diagonal, hd, zString_diagonal]

/-- All-real-time involution exponential, with its identity coefficient explicit. -/
lemma pauli_evolution {n : ℕ} (P : PauliString n) (θ : ℝ) :
    (timeEvolution P.hamiltonian θ : HilbertOperator (Qubits n)) =
      cosine θ • 1 + sine θ • (P.op : HilbertOperator (Qubits n)) := by
  have hP : (P.op : HilbertOperator (Qubits n)) * P.op = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp P.op.property
    rw [Matrix.star_eq_conjTranspose, P.op_isHermitian] at h
    exact h
  change NormedSpace.exp ((-(Complex.I * (θ : ℂ))) •
    (P.op : HilbertOperator (Qubits n))) = _
  open scoped Matrix.Norms.L2Operator in
    exact exp_smul_of_mul_self_eq_one _ hP

end
end QuantumAlg.Trotter.PauliRotation
