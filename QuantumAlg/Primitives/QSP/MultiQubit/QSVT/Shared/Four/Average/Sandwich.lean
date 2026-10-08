/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average
import all QuantumAlg.Components.Gates.Hadamard.Three

/-!
# Connecting native three-Hadamard boundaries to coherent averaging

The full operator identity applies to arbitrary unitary branches. No block
or initialization assumption is used to identify the native boundary gates.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private theorem average_conjugate {width : Nat}
    (A B W : UnitaryOperator (Qubits width)) :
    Gate.HOp.tensor W * phaseControlledDirectSumOperator A B * Gate.HOp.tensor W =
      binaryAverage (W * A * W) (W * B * W) := by
  apply Subtype.ext
  simp only [binaryAverage, phaseHadamardWrapperOperator, Submonoid.coe_mul,
    UnitaryOperator.coe_tensor, phaseControlledDirectSum_eq_tensor_decomp]
  change
    HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) W *
      (HilbertOperator.tensor HilbertOperator.proj0 A +
        HilbertOperator.tensor HilbertOperator.proj1 B) *
      HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) W =
    HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) 1 *
      (HilbertOperator.tensor HilbertOperator.proj0 (W.val * A.val * W.val) +
        HilbertOperator.tensor HilbertOperator.proj1 (W.val * B.val * W.val)) *
      HilbertOperator.tensor (Gate.HOp : HilbertOperator (Qubits 1)) 1
  simp only [Matrix.mul_add, Matrix.add_mul]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- The actual three-Hadamard boundaries realize the complete four-branch averaging operator. -/
theorem threeHadamard_fourBranch_operator {width : Nat} (oracles : OracleModel)
    (A B C D : UnitaryOperator (Qubits (1 + width))) :
    (Gate.Hadamard.three oracles width).binaryMatrix *
      phaseControlledDirectSumOperator (phaseControlledDirectSumOperator A B)
        (phaseControlledDirectSumOperator C D) *
      (Gate.Hadamard.three oracles width).binaryMatrix = threeAverage A B C D := by
  rw [Gate.Hadamard.threeHadamard_matrix, average_conjugate,
    average_conjugate, average_conjugate]
  rfl

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
