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
lemma unmatched_operator (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    ((unmatched (m := m) (n := n) positive phases lastAngle).binaryMatrix
      (UnitarySource.interpretation U true true false)) =
      phaseControlledDirectSumOperator
        ((KnownZero.circuit (m := m) (n := n) positive true (phases.map Prod.fst)).binaryMatrix
          (UnitarySource.interpretation U true true false))
        ((KnownZero.circuit (m := m) (n := n) positive true (lastAngle :: phases.map
          Prod.snd)).binaryMatrix (UnitarySource.interpretation U true true false)) := by
  apply Subtype.ext
  rw [unmatched_matrix, phaseControlledDirectSum_eq_tensor_decomp]
  rfl

/-- Selector projection averages both original phase words without adding source queries. -/
lemma unmatched_plus_block (phases : List (ℝ × ℝ)) (lastAngle : ℝ) :
    phasePlusBlock ((unmatched (m := m) (n := n) positive phases lastAngle).binaryMatrix
      (UnitarySource.interpretation U true true false)) =
      (1 / 2 : ℂ) • (((KnownZero.circuit (m := m) (n := n) positive true
        (phases.map Prod.fst)).binaryMatrix
          (UnitarySource.interpretation U true true false)) : HilbertOperator (Qubits (1 + (m +
          n)))) +
      (1 / 2 : ℂ) • (((KnownZero.circuit (m := m) (n := n) positive true
        (lastAngle :: phases.map Prod.snd)).binaryMatrix
          (UnitarySource.interpretation U true true false)) :
          HilbertOperator (Qubits (1 + (m + n)))) := by
  rw [unmatched_operator, phasePlusBlock_phaseControlledDirectSum]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
