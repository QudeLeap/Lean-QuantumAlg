/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Certified projector reflection operators

These mathematical operators carry exact phase and tensor semantics without
assigning native instructions or oracle access. Executable callers must provide
an implementation in their chosen gate model or an explicit oracle contract.
Projector-controlled NOT uses the same independent projector specification.
-/

section

namespace QuantumAlg

noncomputable section

namespace Gate

theorem X_conjTranspose :
    (Gate.XOp : HilbertOperator (Qubits 1)).conjTranspose =
      (Gate.XOp : HilbertOperator (Qubits 1)) := by
  change ((Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ).conjTranspose =
    (Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ
  rw [Matrix.conjTranspose_permMatrix, Equiv.swap_inv]

theorem X_mul_X :
    (Gate.XOp : HilbertOperator (Qubits 1)) *
      (Gate.XOp : HilbertOperator (Qubits 1)) = 1 := by
  change (Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ *
      (Equiv.swap (0 : Fin (2 ^ 1)) 1).permMatrix ℂ = 1
  rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

end Gate

/-- A finite-dimensional orthogonal projector.  Projectors are raw Hilbert
operators rather than gates; their associated reflections are unitary gates. -/
public structure OrthogonalProjector (n : Nat) where
  /-- The projector matrix. -/
  op : HilbertOperator (Qubits n)
  selfAdjoint : op.conjTranspose = op
  idempotent : op * op = op

namespace OrthogonalProjector

/-- The identity projector. -/
def identity (n : Nat) : OrthogonalProjector n where
  op := 1
  selfAdjoint := by rw [Matrix.conjTranspose_one]
  idempotent := by simp

/-- The rank-one operator `|psi><psi|` associated to a normalized vector. -/
def rankOneOp {n : Nat} (ψ : NormalizedVector (Qubits n)) :
    HilbertOperator (Qubits n) :=
  Matrix.of fun r c => ψ r * starRingEnd ℂ (ψ c)

theorem rankOneOp_conjTranspose {n : Nat}
    (ψ : NormalizedVector (Qubits n)) :
    (rankOneOp ψ).conjTranspose = rankOneOp ψ := by
  ext r c
  simp [rankOneOp, Matrix.conjTranspose_apply, mul_comm]

/-- The rank-one operator acts by taking the `psi` component. -/
theorem rankOneOp_applyVec {n : Nat}
    (ψ : NormalizedVector (Qubits n)) (φ : HilbertVector (Qubits n)) :
    HilbertOperator.applyVec (rankOneOp ψ) φ =
      inner ℂ (ψ : HilbertVector (Qubits n)) φ •
        (ψ : HilbertVector (Qubits n)) := by
  ext r
  rw [HilbertOperator.applyVec_apply]
  simp only [rankOneOp, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.inner_apply, RCLike.inner_apply]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem rankOneOp_idempotent {n : Nat}
    (ψ : NormalizedVector (Qubits n)) :
    rankOneOp ψ * rankOneOp ψ = rankOneOp ψ := by
  have hinner :
      inner ℂ (ψ : HilbertVector (Qubits n))
          (ψ : HilbertVector (Qubits n)) = 1 :=
    inner_self_eq_one_of_norm_eq_one ψ.norm_eq_one
  simp only [PiLp.inner_apply, RCLike.inner_apply] at hinner
  ext r c
  rw [Matrix.mul_apply]
  simp only [rankOneOp, Matrix.of_apply]
  calc
    (∑ x, (ψ r * starRingEnd ℂ (ψ x)) *
        (ψ x * starRingEnd ℂ (ψ c))) =
        (ψ r * starRingEnd ℂ (ψ c)) *
          ∑ x, ψ x * starRingEnd ℂ (ψ x) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    _ = ψ r * starRingEnd ℂ (ψ c) := by rw [hinner, mul_one]

/-- Orthogonal projection onto the span of a normalized vector. -/
def rankOne {n : Nat} (ψ : NormalizedVector (Qubits n)) :
    OrthogonalProjector n where
  op := rankOneOp ψ
  selfAdjoint := rankOneOp_conjTranspose ψ
  idempotent := rankOneOp_idempotent ψ

/-- The rank-one computational-basis projector `|j><j|`. -/
def basisOp {n : Nat} (j : Fin (2 ^ n)) : HilbertOperator (Qubits n) :=
  Matrix.of fun r c => (if r = j then (1 : ℂ) else 0) * (if c = j then (1 : ℂ) else 0)

theorem basisOp_conjTranspose {n : Nat} (j : Fin (2 ^ n)) :
    (basisOp j).conjTranspose = basisOp j := by
  ext r c
  by_cases hr : r = j <;> by_cases hc : c = j <;>
    simp [basisOp, Matrix.conjTranspose_apply, hr, hc]

theorem basisOp_idempotent {n : Nat} (j : Fin (2 ^ n)) :
    basisOp j * basisOp j = basisOp j := by
  ext r c
  rw [Matrix.mul_apply]
  by_cases hr : r = j <;> by_cases hc : c = j <;>
    simp [basisOp, hr, hc]

/-- The computational-basis projector `|j><j|`. -/
def basis {n : Nat} (j : Fin (2 ^ n)) : OrthogonalProjector n where
  op := basisOp j
  selfAdjoint := basisOp_conjTranspose j
  idempotent := basisOp_idempotent j

/-- The computational all-zero basis projector. -/
def zero (n : Nat) : OrthogonalProjector n :=
  basis (0 : Fin (2 ^ n))

/-- Tensor product of orthogonal projectors. -/
def tensor {m n : Nat} (P : OrthogonalProjector m) (Q : OrthogonalProjector n) :
    OrthogonalProjector (m + n) where
  op := HilbertOperator.tensor P.op Q.op
  selfAdjoint := by
    rw [HilbertOperator.conjTranspose_tensor, P.selfAdjoint, Q.selfAdjoint]
  idempotent := by
    rw [HilbertOperator.tensor_mul_tensor, P.idempotent, Q.idempotent]

/-- Projector onto the `|0^a>` ancilla block tensored with the full `n`-qubit
system register. -/
def zeroAncilla (a n : Nat) : OrthogonalProjector (a + n) :=
  tensor (zero a) (identity n)

/-- The reflection `2P - I` associated to an orthogonal projector, certified
as a metadata-free unitary operator. -/
def reflectionOp {n : Nat} (P : OrthogonalProjector n) : UnitaryOperator (Qubits n) :=
  UnitaryOperator.ofMatrix ((2 : ℂ) • P.op - 1) (by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, P.selfAdjoint, Matrix.mul_sub, Matrix.sub_mul,
      P.idempotent]
    module)

theorem reflectionOp_conjTranspose {n : Nat} (P : OrthogonalProjector n) :
    (reflectionOp P : HilbertOperator (Qubits n)).conjTranspose =
      (reflectionOp P : HilbertOperator (Qubits n)) := by
  simp [reflectionOp, UnitaryOperator.ofMatrix, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, P.selfAdjoint]

theorem reflectionOp_sq {n : Nat} (P : OrthogonalProjector n) :
    (reflectionOp P : HilbertOperator (Qubits n)) *
        (reflectionOp P : HilbertOperator (Qubits n)) = 1 := by
  simp [reflectionOp, UnitaryOperator.ofMatrix, Matrix.mul_sub, Matrix.sub_mul,
    P.idempotent]
  module

/-- The complementary orthogonal projector `I - P`. -/
def complement {n : Nat} (P : OrthogonalProjector n) : HilbertOperator (Qubits n) :=
  1 - P.op

theorem mul_complement {n : Nat} (P : OrthogonalProjector n) :
    P.op * complement P = 0 := by
  simp [complement, Matrix.mul_sub, P.idempotent]

theorem complement_mul {n : Nat} (P : OrthogonalProjector n) :
    complement P * P.op = 0 := by
  simp [complement, Matrix.sub_mul, P.idempotent]

theorem complement_sq {n : Nat} (P : OrthogonalProjector n) :
    complement P * complement P = complement P := by
  simp [complement, Matrix.mul_sub, Matrix.sub_mul, P.idempotent]

theorem complement_conjTranspose {n : Nat} (P : OrthogonalProjector n) :
    (complement P).conjTranspose = complement P := by
  simp [complement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, P.selfAdjoint]

/-- The orthogonal projector onto the complement of `P`. -/
def complementProjector {n : Nat} (P : OrthogonalProjector n) :
    OrthogonalProjector n where
  op := complement P
  selfAdjoint := complement_conjTranspose P
  idempotent := complement_sq P

/-- The phase reflection `I - 2P`, which negates the image of `P` and fixes
its orthogonal complement. -/
def phaseReflectionOp {n : Nat} (P : OrthogonalProjector n) :
    UnitaryOperator (Qubits n) :=
  reflectionOp (complementProjector P)

/-- Reflection through a normalized vector: `2|psi><psi| - I`. -/
def rankOneReflectionOp {n : Nat} (ψ : NormalizedVector (Qubits n)) :
    UnitaryOperator (Qubits n) :=
  reflectionOp (rankOne ψ)

/-- Phase reflection about a normalized vector: `I - 2|psi><psi|`. -/
public def rankOnePhaseReflectionOp {n : Nat} (ψ : NormalizedVector (Qubits n)) :
    UnitaryOperator (Qubits n) :=
  phaseReflectionOp (rankOne ψ)

/-- A projector reflection acts as `2P psi - psi` on every vector. -/
theorem reflectionOp_applyVec {n : Nat} (P : OrthogonalProjector n)
    (ψ : HilbertVector (Qubits n)) :
    (reflectionOp P).applyVec ψ =
      (2 : ℂ) • HilbertOperator.applyVec P.op ψ - ψ := by
  have hOp :
      (reflectionOp P : HilbertOperator (Qubits n)) =
        (2 : ℂ) • P.op - 1 := rfl
  change HilbertOperator.applyVec
      (reflectionOp P : HilbertOperator (Qubits n)) ψ = _
  rw [hOp, HilbertOperator.sub_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.one_applyVec]

/-- Reflection through `psi` in rank-one form. -/
theorem rankOneReflectionOp_applyVec {n : Nat}
    (ψ : NormalizedVector (Qubits n)) (φ : HilbertVector (Qubits n)) :
    (rankOneReflectionOp ψ).applyVec φ =
      ((2 : ℂ) * inner ℂ (ψ : HilbertVector (Qubits n)) φ) •
          (ψ : HilbertVector (Qubits n)) - φ := by
  rw [rankOneReflectionOp, reflectionOp_applyVec]
  change (2 : ℂ) • HilbertOperator.applyVec (rankOneOp ψ) φ - φ = _
  rw [rankOneOp_applyVec]
  module

/-- Phase reflection about `psi` in rank-one form. -/
theorem rankOnePhaseReflectionOp_applyVec {n : Nat}
    (ψ : NormalizedVector (Qubits n)) (φ : HilbertVector (Qubits n)) :
    (rankOnePhaseReflectionOp ψ).applyVec φ =
      φ - ((2 : ℂ) * inner ℂ (ψ : HilbertVector (Qubits n)) φ) •
        (ψ : HilbertVector (Qubits n)) := by
  rw [rankOnePhaseReflectionOp, phaseReflectionOp, reflectionOp_applyVec]
  change (2 : ℂ) •
      HilbertOperator.applyVec (1 - (rankOne ψ).op) φ - φ = _
  rw [HilbertOperator.sub_applyVec, HilbertOperator.one_applyVec]
  change (2 : ℂ) •
      (φ - HilbertOperator.applyVec (rankOneOp ψ) φ) - φ = _
  rw [rankOneOp_applyVec]
  module

/-- A projector complement kills vectors already supported on the projector. -/
theorem complement_applyVec_eq_zero_of_projector_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {ψ : HilbertVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op ψ = ψ) :
    HilbertOperator.applyVec (complement P) ψ = 0 := by
  calc
    HilbertOperator.applyVec (complement P) ψ =
        HilbertOperator.applyVec (complement P) (HilbertOperator.applyVec P.op ψ) := by
      rw [hpsi]
    _ = HilbertOperator.applyVec (complement P * P.op) ψ := by
      rw [HilbertOperator.mul_applyVec]
    _ = 0 := by
      rw [complement_mul]
      ext i
      simp [HilbertOperator.applyVec_apply]

/-- A projector kills vectors supported on its complement. -/
theorem projector_applyVec_eq_zero_of_complement_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {ψ : HilbertVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec (complement P) ψ = ψ) :
    HilbertOperator.applyVec P.op ψ = 0 := by
  calc
    HilbertOperator.applyVec P.op ψ =
        HilbertOperator.applyVec P.op (HilbertOperator.applyVec (complement P) ψ) := by
      rw [hpsi]
    _ = HilbertOperator.applyVec (P.op * complement P) ψ := by
      rw [HilbertOperator.mul_applyVec]
    _ = 0 := by
      rw [mul_complement]
      ext i
      simp [HilbertOperator.applyVec_apply]

/-- The reflection through a projector fixes vectors in the projector image. -/
theorem reflectionOp_applyVec_of_projector_applyVec_eq_self {n : Nat}
    (P : OrthogonalProjector n) {ψ : HilbertVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op ψ = ψ) :
    (reflectionOp P).applyVec ψ = ψ := by
  have hOp :
      (reflectionOp P : HilbertOperator (Qubits n)) =
        (2 : ℂ) • P.op + (-1 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
    ext i j
    simp [reflectionOp, UnitaryOperator.ofMatrix, sub_eq_add_neg]
  change HilbertOperator.applyVec (reflectionOp P : HilbertOperator (Qubits n)) ψ = ψ
  rw [hOp, HilbertOperator.add_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec, hpsi]
  ext i
  simp
  ring

/-- The reflection through a projector negates vectors in the complementary
image. -/
theorem reflectionOp_applyVec_of_projector_applyVec_eq_zero {n : Nat}
    (P : OrthogonalProjector n) {ψ : HilbertVector (Qubits n)}
    (hpsi : HilbertOperator.applyVec P.op ψ = 0) :
    (reflectionOp P).applyVec ψ = -ψ := by
  have hOp :
      (reflectionOp P : HilbertOperator (Qubits n)) =
        (2 : ℂ) • P.op + (-1 : ℂ) • (1 : HilbertOperator (Qubits n)) := by
    ext i j
    simp [reflectionOp, UnitaryOperator.ofMatrix, sub_eq_add_neg]
  change HilbertOperator.applyVec (reflectionOp P : HilbertOperator (Qubits n)) ψ = -ψ
  rw [hOp, HilbertOperator.add_applyVec, HilbertOperator.smul_applyVec,
    HilbertOperator.smul_applyVec, HilbertOperator.one_applyVec, hpsi]
  ext i
  simp

/-- Projector-controlled NOT:
`C_P NOT = X ⊗ P + I ⊗ (I-P)`, flipping the leading qubit on the image of `P`. -/
public def controlledNotOp {n : Nat} (P : OrthogonalProjector n) :
    UnitaryOperator (Qubits (1 + n)) :=
  UnitaryOperator.ofMatrix
    (HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) P.op
      + HilbertOperator.tensor (1 : HilbertOperator (Qubits 1)) (complement P))
    (by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      rw [Matrix.conjTranspose_add, HilbertOperator.conjTranspose_tensor,
        HilbertOperator.conjTranspose_tensor, Gate.X_conjTranspose, P.selfAdjoint,
        Matrix.conjTranspose_one, complement_conjTranspose]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
        HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
        Gate.X_mul_X, Matrix.one_mul, Matrix.mul_one,
        P.idempotent, mul_complement, complement_mul, complement_sq]
      simp only [HilbertOperator.tensor_zero, add_zero, Nat.reducePow, mul_one, zero_add]
      rw [← HilbertOperator.tensor_add]
      have hsum : P.op + complement P = 1 := by
        simp [complement]
      rw [hsum, HilbertOperator.one_tensor_one])

end OrthogonalProjector



end

end QuantumAlg

end
