/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Oracle.Reflection

/-!
# Exact paired padding of source phase words

Two zero phases insert one U and one inverse U that cancel exactly. This is
an operator identity for aligning source sequences; it does not erase the
queries or native gates of an executed padded word
[GSLW19, BlockHam.tex:738-745,883-890].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native
noncomputable section

private theorem zero_phase {width : Nat} (P : OrthogonalProjector width) :
    projectorPhaseOp 0 P = 1 := by
  apply Subtype.ext
  simp [projectorPhaseOp, projectorPhaseMatrix, OrthogonalProjector.complement]

/-- Two zero source phases preserve the full operator on every state and reference. -/
theorem sourceWord_two_zero {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (phases : List ℝ) :
    sourceWord U left right (0 :: 0 :: phases) = sourceWord U left right phases := by
  by_cases even : phases.length % 2 = 0
  · have first : (phases.length + 1) % 2 ≠ 0 := by omega
    have second : (phases.length + 1 + 1) % 2 = 0 := by omega
    simp [sourceWord, zero_phase, first, second]
  · have first : (phases.length + 1) % 2 = 0 := by omega
    have second : (phases.length + 1 + 1) % 2 ≠ 0 := by omega
    simp [sourceWord, zero_phase, first, second]

/-- Add only cancelling pairs, preserving the parity of the original source list. -/
def padPairs : Nat → List ℝ → List ℝ
  | 0, phases => phases
  | count + 1, phases => 0 :: 0 :: padPairs count phases

/-- Padding length is explicit and remains visible to all native resource formulas. -/
theorem padPairs_length (count : Nat) (phases : List ℝ) :
    (padPairs count phases).length = 2 * count + phases.length := by
  induction count with
  | zero => simp [padPairs]
  | succ count ih => simp [padPairs, ih]; omega

/-- Paired padding preserves the independent source operator exactly. -/
theorem sourceWord_padPairs {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (count : Nat) (phases : List ℝ) :
    sourceWord U left right (padPairs count phases) = sourceWord U left right phases := by
  induction count with
  | zero => rfl
  | succ count ih => rw [padPairs, sourceWord_two_zero, ih]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Native
