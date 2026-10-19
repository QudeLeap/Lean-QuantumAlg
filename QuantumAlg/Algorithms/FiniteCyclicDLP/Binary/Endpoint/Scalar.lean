/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Space
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Resources

/-!
# Reviewed scalar resources of the actual sequential finite-cyclic endpoint

The formulas are projections of the same complete event and live-space
allowances. All terminal reset gates are included; checked recovery contributes
only classical operations [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The native gate ceilings have the reviewed polynomial forms. -/
public lemma widthResourceBounds (P : KnownOrderProblem G) :
    (publicCoordinates P).cnotGates ≤ sampleCount P *
      (2 * (OrderPreparation.width P) ^ 2 + 4 * OrderPreparation.width P +
        6 * (OrderPreparation.width P / 2)) ∧
    (publicCoordinates P).singleQubitGates ≤ sampleCount P *
      (3 * (OrderPreparation.width P) ^ 2 + 23 * OrderPreparation.width P +
        Binary.groupWidth P) := by
  have cnot := Reusable.eventBudget_cnot_le P (sampleCount P)
    (OrderExecution.canonicalExpansion P)
  have single := Reusable.eventBudget_singleQubit_le P (sampleCount P)
    (OrderExecution.canonicalExpansion P)
  rw [Reusable.reusableDLP_eventBudget_cnot_count] at cnot
  rw [Reusable.reusableDLP_eventBudget_singleQubit_count] at single
  exact ⟨cnot, single⟩

/-- Every actual complete-run path obeys the displayed native gate and query ceilings. -/
public lemma code_nativeCounts_le_width (P : KnownOrderProblem G) (path : (code P).Path) :
    ResourcePool.count (model := Reusable.model P) (.gate .cnot)
      ((code P).resourcePool path) ≤ sampleCount P *
        (2 * (OrderPreparation.width P) ^ 2 + 4 * OrderPreparation.width P +
          6 * (OrderPreparation.width P / 2)) ∧
    ResourcePool.count (model := Reusable.model P) (.gate .singleQubit)
      ((code P).resourcePool path) ≤ sampleCount P *
        (3 * (OrderPreparation.width P) ^ 2 + 23 * OrderPreparation.width P +
          Binary.groupWidth P) ∧
    ResourcePool.count (model := Reusable.model P) (.oracle .ux)
      ((code P).resourcePool path) ≤ sampleCount P := by
  have actual := ResourcePool.le_iff_count.mp (binaryEndpoint_code_pool_le P path)
  obtain ⟨cnot, single⟩ := widthResourceBounds P
  refine ⟨?_, ?_, ?_⟩
  · exact (actual (.gate .cnot)).trans ((binaryEndpoint_eventBudget_cnot_count P).le.trans cnot)
  · exact (actual (.gate .singleQubit)).trans
      ((binaryEndpoint_eventBudget_singleQubit_count P).le.trans single)
  · exact (actual (.oracle .ux)).trans_eq (binaryEndpoint_eventBudget_ux_count P)

/-- Abstract group multiplications and squarings retain their separate access coordinate. -/
public lemma code_groupOperations_le_width (P : KnownOrderProblem G)
    (path : (code P).Path) :
    ResourcePool.count
      (OrderRecovery.Native.groupOperationEvent (oracles := Binary.Oracle.model P) P)
      ((code P).resourcePool path) ≤ 2 * sampleCount P * OrderPreparation.width P := by
  have actual := ResourcePool.le_iff_count.mp (binaryEndpoint_code_pool_le P path)
    (OrderRecovery.Native.groupOperationEvent (oracles := Binary.Oracle.model P) P)
  rw [binaryEndpoint_eventBudget_groupOperation_count] at actual
  have budget : (publicCoordinates P).groupOperations ≤
      2 * sampleCount P * OrderPreparation.width P := by
    simp only [publicCoordinates]
    split_ifs
    · exact Nat.zero_le _
    · exact le_of_eq (by ring)
  exact actual.trans budget

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
