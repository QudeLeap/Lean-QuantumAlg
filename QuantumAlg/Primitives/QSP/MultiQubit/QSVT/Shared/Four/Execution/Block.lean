/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution.Matrix

/-!
# The standard output block of complete native four-branch execution

The output is the one-quarter weighted sum of the original four branch
blocks. The imaginary branches retain their explicit factor i.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private theorem phasePlusBlock_scaled {width : Nat} (scalar : ℂ)
    (unit : Complex.normSq scalar = 1) (V : UnitaryOperator (Qubits (1 + width))) :
    phasePlusBlock (phaseScaledOperator scalar unit V) = scalar • phasePlusBlock V := by
  ext row column
  simp only [phasePlusBlock, phaseScaledOperator_coe, phaseScaledOperatorRaw,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

private theorem projectedBlock_smul (m n : Nat) (scalar : ℂ)
    (V : HilbertOperator (Qubits (m + n))) :
    projectedBlock m n (scalar • V) = scalar • projectedBlock m n V := rfl

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- The executed circuit's output block is the exact weighted sum of its four source branches. -/
theorem complexWord_projected_block (phases : List ((ℝ × ℝ) × (ℝ × ℝ)))
    (realAngle imaginaryAngle realConstant imaginaryConstant : ℝ) :
    projectedBlock (1 + (1 + (1 + m))) n
      (reassociateThree (complexWord U positive phases realAngle imaginaryAngle
        realConstant imaginaryConstant).binaryMatrix) =
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock
        (initializedBranch U positive (phases.map fun a => a.1.1) realConstant)) +
      (1 / 4 : ℂ) • projectedBlock m n (phasePlusBlock
        (initializedBranch U positive (realAngle :: phases.map fun a => a.1.2) 1)) +
      ((1 / 4 : ℂ) • Complex.I • projectedBlock m n (phasePlusBlock
        (initializedBranch U positive (phases.map fun a => a.2.1) imaginaryConstant)) +
      (1 / 4 : ℂ) • Complex.I • projectedBlock m n (phasePlusBlock
        (initializedBranch U positive (imaginaryAngle :: phases.map fun a => a.2.2) 1))) := by
  rw [complexWord_average_operator, threeAverage_projected_block,
    phasePlusBlock_scaled, phasePlusBlock_scaled, projectedBlock_smul, projectedBlock_smul]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
