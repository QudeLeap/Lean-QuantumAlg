/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Shared.Unmatched.Resources

/-!
# Assembling two independently synthesized opposite-parity words

The phase lists retain their own source ordering. Equal tails share each
query, and the longer list contributes just its final unmatched slot.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Shared
noncomputable section

private lemma zip_exact (left right : List ℝ) (same : left.length = right.length) :
    (left.zip right).map Prod.fst = left ∧
      (left.zip right).map Prod.snd = right ∧ (left.zip right).length = left.length := by
  induction left generalizing right with
  | nil =>
      have empty : right = [] := by simpa using same.symm
      subst right
      simp
  | cons head tail ih =>
      cases right with
      | nil => simp at same
      | cons other rest =>
          have equal : tail.length = rest.length := by simpa using same
          obtain ⟨first, second, count⟩ := ih rest equal
          simp only [List.zip_cons_cons, List.map_cons, first, second, List.length_cons, count,
            and_self]

/-- Opposite-parity source lists of neighboring lengths share all but the final query slot. -/
lemma exists_unmatched_assembly {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (positive : 0 < n) (short long : List ℝ) (lengths : long.length = short.length + 1) :
    ∃ phases : List (ℝ × ℝ), ∃ lastAngle : ℝ,
      phases.length = short.length ∧
      (((unmatched (m := m) (n := n) positive phases lastAngle).binaryMatrix
        (UnitarySource.interpretation U true true false)) :
        HilbertOperator (Qubits (1 + (1 + (m + n))))) =
        Native.branchMatrix ((KnownZero.circuit (m := m) (n := n) positive true short).binaryMatrix
          (UnitarySource.interpretation U true true false))
          ((KnownZero.circuit (m := m) (n := n) positive true long).binaryMatrix
            (UnitarySource.interpretation U true true false)) ∧
      (unmatched (m := m) (n := n) positive phases lastAngle).eventCost
        = unmatchedBudget (m := m) (n := n) short.length ∧
      ResourcePool.count
        (model := .quantum AlgorithmGate.model (UnitarySource.model (m + n) true true false))
        (.oracle UnitarySource.Coordinate.controlled)
        (unmatched (m := m) (n := n) positive phases lastAngle).eventCost = 1 := by
  cases long with
  | nil => simp at lengths
  | cons head tail =>
      have equal : short.length = tail.length := by simp only [List.length_cons] at lengths; omega
      obtain ⟨first, second, count⟩ := zip_exact short tail equal
      refine ⟨short.zip tail, head, count, ?_, ?_, ?_⟩
      · rw [unmatched_matrix, first, second]
      · rw [unmatched_events, count]
      · exact unmatched_controlled_queries (m := m) (n := n) positive _ _

end
end QuantumAlg.QSP.MultiQubit.QSVT.Shared
