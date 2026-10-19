/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Matrix
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution.Block

/-!
# The standard output block of complete native four-branch execution

The output is the one-quarter weighted sum of the original four branch
blocks. The imaginary branches retain their explicit factor i.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))

/-- The executed circuit's output block is the exact weighted sum of its four source branches. -/
lemma totalComplexWord_projected_block (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    projectedBlock (1 + (1 + (1 + m))) n
      (reassociateThree ((complexWord (m := m) (n := n) phases realAngle imaginaryAngle
        realConstant imaginaryConstant).binaryMatrix
          (UnitarySource.interpretation U true true false))) =
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock
        (initializedBranch U (phases.map fun a => a.1.1) realConstant)) +
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock
        (initializedBranch U (realAngle :: phases.map fun a => a.1.2) 1)) +
      ((1 / 4 : ℂ) • Complex.I • projectedBlock m n (phasePlusBlock
        (initializedBranch U (phases.map fun a => a.2.1) imaginaryConstant)) +
      (1 / 4 : ℂ) • Complex.I • projectedBlock m n (phasePlusBlock
        (initializedBranch U (imaginaryAngle :: phases.map fun a => a.2.2) 1))) := by
  rw [totalComplexWord_average_operator, threeAverage_projected_block,
    phasePlusBlock_scaled, phasePlusBlock_scaled, projectedBlock_smul, projectedBlock_smul]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
