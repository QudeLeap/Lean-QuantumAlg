/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Assembly

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Total.Four.Execution.Matrix
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched.Assembly

/-!
# Assembling four independently synthesized phase lists

The two short lists have the same length. Each long list contributes one
unmatched head phase, while all four tails share their source query slots.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
open SharedFour
noncomputable section

/-- Four independently specified source words are realized by one actual shared native execution. -/
theorem exists_totalComplexWord_for_lists {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (realShort realLong imaginaryShort imaginaryLong : List ℝ)
    (realLength : realLong.length = realShort.length + 1)
    (imaginaryShortLength : imaginaryShort.length = realShort.length)
    (imaginaryLongLength : imaginaryLong.length = realShort.length + 1)
    (realConstant imaginaryConstant : ℝ) :
    ∃ phases : List ((ℝ × ℝ) × (ℝ × ℝ)), ∃ realAngle imaginaryAngle : ℝ,
      phases.length = realShort.length ∧
      (complexWord U phases realAngle imaginaryAngle
        realConstant imaginaryConstant).binaryMatrix =
        threeAverage
          (initializedBranch U realShort realConstant)
          (initializedBranch U realLong 1)
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U imaginaryShort imaginaryConstant))
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U imaginaryLong 1)) ∧
      (complexWord U phases realAngle imaginaryAngle
        realConstant imaginaryConstant).eventCost = complexBudget U realShort.length := by
  cases realLong with
  | nil => simp at realLength
  | cons realHead realTail =>
      cases imaginaryLong with
      | nil => simp at imaginaryLongLength
      | cons imaginaryHead imaginaryTail =>
          have realTailLength : realTail.length = realShort.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using realLength
          have imaginaryTailLength : imaginaryTail.length = realShort.length := by
            simpa only [List.length_cons, Nat.add_right_cancel_iff] using imaginaryLongLength
          obtain ⟨a, b, c, d, count⟩ := pack_lists realShort realTail
            imaginaryShort imaginaryTail realTailLength imaginaryShortLength imaginaryTailLength
          refine ⟨(realShort.zip realTail).zip (imaginaryShort.zip imaginaryTail),
            realHead, imaginaryHead, count, ?_, ?_⟩
          · rw [totalComplexWord_average_operator, a, b, c, d]
          · rw [totalComplexWord_events, count]

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero.Total.Four
