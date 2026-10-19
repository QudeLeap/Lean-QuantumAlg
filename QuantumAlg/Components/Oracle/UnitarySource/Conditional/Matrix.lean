/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.UnitarySource.Conditional
import all QuantumAlg.Components.Control
import all QuantumAlg.Components.Gates.Operator

/-!
# Full conditional inverse from ordinary inverse and controlled forward access

The exact operator proof retains the untouched selector branch and every
source state. It does not add a controlled-inverse query to the access model.
-/

namespace QuantumAlg.UnitarySource.Conditional
noncomputable section

private lemma x_proj_zero :
    (Gate.XOp : HilbertOperator (Qubits 1)) * HilbertOperator.proj0 *
      (Gate.XOp : HilbertOperator (Qubits 1)) = HilbertOperator.proj1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, HilbertOperator.proj0, HilbertOperator.proj1,
      Matrix.mul_apply]

private lemma x_proj_one :
    (Gate.XOp : HilbertOperator (Qubits 1)) * HilbertOperator.proj1 *
      (Gate.XOp : HilbertOperator (Qubits 1)) = HilbertOperator.proj0 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, HilbertOperator.proj0, HilbertOperator.proj1,
      Matrix.mul_apply]

private lemma swap_control {width : Nat} (A B : HilbertOperator (Qubits width)) :
    HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits width)) *
      (HilbertOperator.tensor HilbertOperator.proj0 A +
        HilbertOperator.tensor HilbertOperator.proj1 B) *
      HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1))
        (1 : HilbertOperator (Qubits width)) =
      HilbertOperator.tensor HilbertOperator.proj0 B +
        HilbertOperator.tensor HilbertOperator.proj1 A := by
  rw [Matrix.mul_add, Matrix.add_mul]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  rw [x_proj_zero, x_proj_one]
  simp only [Matrix.one_mul, Matrix.mul_one]
  exact add_comm _ _

/-- The actual expanded word is precisely conditional inverse access on the whole source. -/
lemma inverse_matrix {width : Nat} (U : UnitaryOperator (Qubits width)) :
    ((inverse width).binaryMatrix
      (interpretation U true true false)) = UnitaryOperator.controlledQubits U⁻¹ := by
  rw [inverse, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, sourceInverse,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_binaryMatrix, Binary.circuit_matrix,
    controlled_matrix]
  simp only [selectorX, Gate.singleQubitAt_first_binaryMatrix, ↓reduceIte]
  apply Subtype.ext
  change HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
      ((U⁻¹ : UnitaryOperator (Qubits width)) : HilbertOperator (Qubits width)) *
    (HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) 1 *
      ((UnitaryOperator.controlledQubits U : HilbertOperator (Qubits (1 + width))) *
        HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) 1)) = _
  rw [← Matrix.mul_assoc (HilbertOperator.tensor (Gate.XOp : HilbertOperator (Qubits 1)) 1),
    UnitaryOperator.coe_controlledQubits, swap_control,
    UnitaryOperator.coe_controlledQubits, Matrix.mul_add,
    HilbertOperator.tensor_mul_tensor, HilbertOperator.tensor_mul_tensor]
  have cancellation : ((U⁻¹ : UnitaryOperator (Qubits width)) : HilbertOperator (Qubits width)) *
      (U : HilbertOperator (Qubits width)) = 1 :=
    congrArg (fun operator : UnitaryOperator (Qubits width) => operator.val) (inv_mul_cancel U)
  rw [cancellation]
  simp only [Matrix.one_mul, Matrix.mul_one]

end
end QuantumAlg.UnitarySource.Conditional
