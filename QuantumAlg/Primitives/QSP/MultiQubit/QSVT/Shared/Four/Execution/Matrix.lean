/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Sandwich
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Block

/-!
# Complete native execution realizes the intrinsic four-branch average

All three ancilla boundaries and the imaginary relative phase are included
in the same executed word before projecting its standard output block.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private theorem branchMatrix_smul {width : Nat} (scalar : ℂ)
    (A B : HilbertOperator (Qubits width)) :
    Native.branchMatrix (scalar • A) (scalar • B) = scalar • Native.branchMatrix A B := by
  ext row column
  simp only [Native.branchMatrix, HilbertOperator.tensor_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- Full native execution before boundary Hadamards is the exact phase-scaled direct sum. -/
theorem complexCore_operator (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexCore U positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).binaryMatrix =
      phaseControlledDirectSumOperator
        (phaseControlledDirectSumOperator
          (initializedBranch U positive (phases.map fun a => a.1.1) realConstant)
          (initializedBranch U positive (realAngle :: phases.map fun a => a.1.2) 1))
        (phaseControlledDirectSumOperator
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U positive (phases.map fun a => a.2.1) imaginaryConstant))
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U positive (imaginaryAngle :: phases.map fun a => a.2.2) 1))) := by
  apply Subtype.ext
  rw [complexCore_matrix]
  repeat rw [phaseControlledDirectSum_eq_tensor_decomp]
  simp only [phaseScaledOperator_coe, phaseScaledOperatorRaw]
  change Native.branchMatrix (Native.branchMatrix _ _) (Complex.I • Native.branchMatrix _ _) =
    Native.branchMatrix (Native.branchMatrix _ _)
      (Native.branchMatrix (Complex.I • _) (Complex.I • _))
  rw [branchMatrix_smul]

/-- The complete native word realizes the intrinsic average, including all relative phases. -/
theorem complexWord_average_operator (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    (complexWord U positive phases realAngle imaginaryAngle
      realConstant imaginaryConstant).binaryMatrix =
      threeAverage
        (initializedBranch U positive (phases.map fun a => a.1.1) realConstant)
        (initializedBranch U positive (realAngle :: phases.map fun a => a.1.2) 1)
        (phaseScaledOperator Complex.I complex_normSq_I
          (initializedBranch U positive (phases.map fun a => a.2.1) imaginaryConstant))
        (phaseScaledOperator Complex.I complex_normSq_I
          (initializedBranch U positive (imaginaryAngle :: phases.map fun a => a.2.2) 1)) := by
  rw [complexWord, wrap, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, complexCore_operator, ← mul_assoc]
  exact threeHadamard_fourBranch_operator (UnitarySource.model U true true false) _ _ _ _

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
