/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Diagonal
import all QuantumAlg.Core.Base.Gate.Placement.Canonical

/-!
# Full coherent semantics of the native rotation selector

The target is the independently specified diagonal operator, applying the
zero angle when the selector is zero and the one angle otherwise. Equality
on the full matrix preserves relative phase and arbitrary correlations.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex
noncomputable section

/-- Exact scalar of the standard Z rotation on its original target bit. -/
def weight (angle : ℝ) (bit : Fin 2) : ℂ :=
  if bit = 0 then Complex.exp ((-(angle / 2) : ℝ) * Complex.I)
    else Complex.exp ((angle / 2 : ℝ) * Complex.I)

private theorem rotation_diagonal (angle : ℝ) :
    (rotZStdOp angle : HilbertOperator (Qubits 1)) = Matrix.diagonal (weight angle) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [rotZStdOp, rotZOp, weight]

private theorem token_diagonal (angle : ℝ) :
    ((AlgorithmGate.model.operator (.singleQubit (rotZStdOp angle))).val :
      HilbertOperator (QuantumSignature.qubits 1).register) =
      Matrix.diagonal (fun basis => weight angle (QuantumSignature.qubitsIndexEquiv 1 basis)) := by
  ext row column
  change (rotZStdOp angle : HilbertOperator (Qubits 1))
    (QuantumSignature.qubitsIndexEquiv 1 row) (QuantumSignature.qubitsIndexEquiv 1 column) = _
  rw [rotation_diagonal]
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]

private theorem placed_diagonal (oracles : OracleModel) (angle : ℝ) :
    ((singleQubitAt layout oracles (rotZStdOp angle) 1 rfl).matrix :
      HilbertOperator layout.register) = Matrix.diagonal (fun basis => weight angle (basis 1)) := by
  let application := singleQubitApplication layout (rotZStdOp angle) 1 rfl
  have selected (basis : layout.Basis) :
      QuantumSignature.qubitsIndexEquiv 1 (application.basisEquiv basis).1 = basis 1 := by
    have coordinates : (application.basisEquiv basis).1 = fun _ => basis 1 := by
      funext index
      fin_cases index
      apply Fin.ext
      rfl
    rw [coordinates]
    generalize basis 1 = bit
    fin_cases bit <;> rfl
  refine (application.application_operator_diagonal
    (fun basis => weight angle (QuantumSignature.qubitsIndexEquiv 1 basis))
    (token_diagonal angle)).trans ?_
  apply congrArg Matrix.diagonal
  funext basis
  rw [selected]

private theorem conjugate_diagonal (register : Register)
    (permutation : Equiv.Perm register.Index) (involution : Function.Involutive permutation)
    (values : register.Index → ℂ) :
    ((UnitaryOperator.ofPerm (R := register) permutation).val * Matrix.diagonal values) *
      (UnitaryOperator.ofPerm (R := register) permutation).val =
      Matrix.diagonal (fun basis => values (permutation basis)) := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, UnitaryOperator.ofPerm_entry]
  rw [Finset.sum_eq_single (permutation row)]
  · rw [involution]
    by_cases same : row = column <;> simp [same]
  · intro other _ different
    simp [Ne.symm different]
  · simp

private theorem weight_product (zeroAngle oneAngle : ℝ) (control target : Fin 2) :
    weight ((zeroAngle - oneAngle) / 2) (control + target) *
      weight ((zeroAngle + oneAngle) / 2) target =
      weight (if control = 0 then zeroAngle else oneAngle) target := by
  fin_cases control <;> fin_cases target <;>
    simp [weight, ← Complex.exp_add] <;> congr 1 <;> ring

/-- The actual native word has exactly the independently specified coherent branch phases. -/
theorem circuit_matrix (oracles : OracleModel) (zeroAngle oneAngle : ℝ) :
    ((circuit oracles zeroAngle oneAngle).matrix : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis =>
        weight (if basis 0 = 0 then zeroAngle else oneAngle) (basis 1)) := by
  simp only [circuit, UnitaryCircuit.seq_matrix, Submonoid.coe_mul,
    UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator,
    AlgorithmGate.cnot_operator_ofPerm, placed_diagonal]
  have involution : Function.Involutive AlgorithmGate.cnotPermutation := by
    intro basis
    simp [AlgorithmGate.cnotPermutation]
  rw [← mul_assoc, ← mul_assoc,
    conjugate_diagonal layout.register AlgorithmGate.cnotPermutation involution,
    Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext basis
  have selected := congrFun (AlgorithmGate.cnotPermutation_apply basis) (1 : Fin 2)
  exact (congrArg (fun bit : Fin 2 => weight ((zeroAngle - oneAngle) / 2) bit *
    weight ((zeroAngle + oneAngle) / 2) (basis 1)) selected).trans
    (weight_product zeroAngle oneAngle (basis 0) (basis 1))

end
end QuantumAlg.Gate.Rotation.Multiplex
