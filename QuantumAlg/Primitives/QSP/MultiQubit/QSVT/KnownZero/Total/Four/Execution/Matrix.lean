/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution.Matrix
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Sandwich
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Average.Block

/-!
# Complete native execution realizes the intrinsic four-branch average

All three ancilla boundaries and the imaginary relative phase are included
in the same executed word before projecting its standard output block.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

/-- Full native execution before boundary Hadamards is the exact phase-scaled direct sum. -/
lemma totalComplexCore_operator (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    ((complexCore (m := m) (n := n) phases realAngle imaginaryAngle
      realConstant imaginaryConstant).binaryMatrix
        (UnitarySource.interpretation U true true false)) =
      phaseControlledDirectSumOperator
        (phaseControlledDirectSumOperator
          (initializedBranch U (phases.map fun a => a.1.1) realConstant)
          (initializedBranch U (realAngle :: phases.map fun a => a.1.2) 1))
        (phaseControlledDirectSumOperator
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U (phases.map fun a => a.2.1) imaginaryConstant))
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U (imaginaryAngle :: phases.map fun a => a.2.2) 1))) := by
  apply Subtype.ext
  rw [totalComplexCore_matrix]
  repeat rw [phaseControlledDirectSum_eq_tensor_decomp]
  simp only [phaseScaledOperator_coe, phaseScaledOperatorRaw]
  change Native.branchMatrix (Native.branchMatrix _ _) (Complex.I • Native.branchMatrix _ _) =
    Native.branchMatrix (Native.branchMatrix _ _)
      (Native.branchMatrix (Complex.I • _) (Complex.I • _))
  rw [branchMatrix_smul]

/-- The complete native word realizes the intrinsic average, including all relative phases. -/
lemma totalComplexWord_average_operator (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    ((complexWord (m := m) (n := n) phases realAngle imaginaryAngle
      realConstant imaginaryConstant).binaryMatrix
        (UnitarySource.interpretation U true true false)) =
      threeAverage
        (initializedBranch U (phases.map fun a => a.1.1) realConstant)
        (initializedBranch U (realAngle :: phases.map fun a => a.1.2) 1)
        (phaseScaledOperator Complex.I complex_normSq_I
          (initializedBranch U (phases.map fun a => a.2.1) imaginaryConstant))
        (phaseScaledOperator Complex.I complex_normSq_I
          (initializedBranch U (imaginaryAngle :: phases.map fun a => a.2.2) 1)) := by
  rw [complexWord, wrap, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, totalComplexCore_operator, ← mul_assoc]
  exact threeHadamard_fourBranch_operator (UnitarySource.model (m + n) true true false) _ _ _ _
    (UnitarySource.interpretation U true true false)

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
