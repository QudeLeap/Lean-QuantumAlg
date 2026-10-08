/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average

/-!
# The coherent average of the two actual unequal-length words

Projecting the selector onto its plus state averages the independently
specified branch words. The matrix is obtained from the actual shared circuit.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

variable {m n : Nat} (U : UnitaryOperator (Qubits (m + n))) (positive : 0 < n)

/-- The executed unequal-length word is the intrinsic direct sum of its native branches. -/
theorem unmatched_operator (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    (unmatched U positive phases lastAngle).binaryMatrix =
      phaseControlledDirectSumOperator
        (KnownZero.circuit U positive true (phases.map Prod.fst)).binaryMatrix
        (KnownZero.circuit U positive true (lastAngle :: phases.map Prod.snd)).binaryMatrix := by
  apply Subtype.ext
  rw [unmatched_matrix, phaseControlledDirectSum_eq_tensor_decomp]
  rfl

/-- Selector projection averages both original phase words without adding source queries. -/
theorem unmatched_plus_block (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    phasePlusBlock (unmatched U positive phases lastAngle).binaryMatrix =
      (1 / 2 : ℂ) • ((KnownZero.circuit U positive true
        (phases.map Prod.fst)).binaryMatrix : HilbertOperator (Qubits (1 + (m + n)))) +
      (1 / 2 : ℂ) • ((KnownZero.circuit U positive true
        (lastAngle :: phases.map Prod.snd)).binaryMatrix :
          HilbertOperator (Qubits (1 + (m + n)))) := by
  rw [unmatched_operator, phasePlusBlock_phaseControlledDirectSum]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
