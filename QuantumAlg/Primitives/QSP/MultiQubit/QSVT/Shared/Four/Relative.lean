/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Word
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary

/-!
# Actual relative imaginary phase on the outer selector

One native S gate multiplies precisely the imaginary branches by i before
averaging. Its phase is retained as an operator equality, not discarded as a
global phase [GSLW19, BlockHam.tex:1957].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private lemma s_zero : (Gate.SOp : HilbertOperator (Qubits 1)) * HilbertOperator.proj0 =
    HilbertOperator.proj0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Gate.SOp, HilbertOperator.proj0, Matrix.mul_apply]

private lemma s_one : (Gate.SOp : HilbertOperator (Qubits 1)) * HilbertOperator.proj1 =
    Complex.I • HilbertOperator.proj1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Gate.SOp, HilbertOperator.proj1, Matrix.mul_apply]

/-- One actual native gate distinguishes imaginary from real branches coherently. -/
def relative (oracles : OracleModel) (width : Nat) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout :=
  Gate.singleQubitAt (QuantumSignature.qubits (1 + width)).canonicalPlacement.layout
    oracles Gate.SOp (0 : Fin (1 + width)) rfl

/-- The full operator multiplies only the selector-one block by the required relative i. -/
lemma relative_branch_matrix (oracles : OracleModel) (width : Nat)
    (A B : HilbertOperator (Qubits width)) (environment : oracles.Interpretation) :
    (((relative oracles width).binaryMatrix environment) : HilbertOperator (Qubits (1 + width))) *
      Native.branchMatrix A B = Native.branchMatrix A (Complex.I • B) := by
  rw [relative, Gate.singleQubitAt_first_binaryMatrix]
  change HilbertOperator.tensor (Gate.SOp : HilbertOperator (Qubits 1)) 1 *
    (HilbertOperator.tensor HilbertOperator.proj0 A +
      HilbertOperator.tensor HilbertOperator.proj1 B) = _
  rw [Matrix.mul_add, HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor,
    s_zero, s_one]
  simp only [Matrix.one_mul, Native.branchMatrix]
  apply congrArg (fun operator => HilbertOperator.tensor HilbertOperator.proj0 A + operator)
  ext row column
  simp only [HilbertOperator.tensor_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The relative phase is charged as one native one-qubit occurrence. -/
lemma relative_native_events (oracles : OracleModel) (width : Nat) :
    (relative oracles width).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := rfl

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
