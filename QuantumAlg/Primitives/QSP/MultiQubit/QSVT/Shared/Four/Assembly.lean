/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Four.Execution.Matrix
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched.Assembly

/-!
# Assembling four independently synthesized phase lists

The two short lists have the same length. Each long list contributes one
unmatched head phase, while all four tails share their source query slots.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
noncomputable section

private theorem pack_lists (A B C D : List ℝ) (hB : B.length = A.length)
    (hC : C.length = A.length) (hD : D.length = A.length) :
    let phases := (A.zip B).zip (C.zip D)
    phases.map (fun a => a.1.1) = A ∧ phases.map (fun a => a.1.2) = B ∧
      phases.map (fun a => a.2.1) = C ∧ phases.map (fun a => a.2.2) = D ∧
      phases.length = A.length := by
  obtain ⟨a, b, ab⟩ := Shared.zip_exact A B hB.symm
  obtain ⟨c, d, cd⟩ := Shared.zip_exact C D (hC.trans hD.symm)
  have same : (A.zip B).length = (C.zip D).length := by rw [ab, cd, hC]
  have first : ((A.zip B).zip (C.zip D)).map Prod.fst = A.zip B :=
    List.map_fst_zip same.le
  have second : ((A.zip B).zip (C.zip D)).map Prod.snd = C.zip D :=
    List.map_snd_zip same.ge
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map Prod.fst) first).trans a
  · simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map Prod.snd) first).trans b
  · simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map Prod.fst) second).trans c
  · simpa only [List.map_map, Function.comp_def] using
      (congrArg (List.map Prod.snd) second).trans d
  · simp only [List.length_zip, same, min_self, cd, hC]

/-- Four independently specified source words are realized by one actual shared native execution. -/
theorem exists_complexWord_for_lists {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (positive : 0 < n) (realShort realLong imaginaryShort imaginaryLong : List ℝ)
    (realLength : realLong.length = realShort.length + 1)
    (imaginaryShortLength : imaginaryShort.length = realShort.length)
    (imaginaryLongLength : imaginaryLong.length = realShort.length + 1)
    (realConstant imaginaryConstant : ℝ) :
    ∃ phases : List ((ℝ × ℝ) × (ℝ × ℝ)), ∃ realAngle imaginaryAngle : ℝ,
      phases.length = realShort.length ∧
      (complexWord U positive phases realAngle imaginaryAngle
        realConstant imaginaryConstant).binaryMatrix =
        threeAverage
          (initializedBranch U positive realShort realConstant)
          (initializedBranch U positive realLong 1)
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U positive imaginaryShort imaginaryConstant))
          (phaseScaledOperator Complex.I complex_normSq_I
            (initializedBranch U positive imaginaryLong 1)) ∧
      (complexWord U positive phases realAngle imaginaryAngle
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
          · rw [complexWord_average_operator, a, b, c, d]
          · rw [complexWord_events, count]

end
end QuantumAlg.QSP.MultiQubit.QSVT.SharedFour
