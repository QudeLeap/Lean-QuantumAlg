/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Cycle
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Oracle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar

/-!
# Width bounds for the complete finite-cyclic discrete-logarithm execution

The actual known-order preparation retains its native gate word. Its generic
gap bounds give scalar ceilings without evaluating a bit-position table.
The same complete batch includes the sampler and classical recovery tail.
Native group systems retain their actual
dimension rather than being assigned a binary encoding.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The actual group system retains the ambient group's cardinality as its
dimension. No binary encoding or subgroup-generation premise is needed. -/
public lemma finiteCyclicDLP_groupDimension_eq_card :
    (OrderOracle.workspaceDimension G).val = Fintype.card G := rfl

/-- When the advertised generator covers the whole group, its native system
has the known order as its dimension. The original algorithm also admits
ambient groups without this supplementary premise. -/
public lemma finiteCyclicDLP_groupDimension_eq_order (P : KnownOrderProblem G)
    (covers : ∀ target : G, target ∈ Subgroup.zpowers P.generator) :
    (OrderOracle.workspaceDimension G).val = P.order := by
  classical
  change Fintype.card G = P.order
  rw [P.order_eq_orderOf]
  simpa only [Nat.card_eq_fintype_card] using
    (orderOf_eq_card_of_forall_mem_zpowers covers).symm

/-- Independent native gate ceilings use only the symbolic
register width and the original retry count. -/
public lemma finiteCyclicDLP_widthResourceBounds (P : KnownOrderProblem G) :
    (publicCoordinates P).cnotGates ≤ sampleCount P *
      (6 * OrderPreparation.width P + 4 * (OrderPreparation.width P).choose 2 +
        6 * (OrderPreparation.width P / 2)) ∧
    (publicCoordinates P).singleQubitGates ≤ sampleCount P *
      (24 * OrderPreparation.width P + 6 * (OrderPreparation.width P).choose 2) := by
  obtain ⟨single, cnot, _depth⟩ := OrderPreparation.orderPreparation_scalarBounds P
    (OrderExecution.canonicalExpansion P)
  constructor
  · change sampleCount P * _ ≤ sampleCount P * _
    apply Nat.mul_le_mul_left (sampleCount P)
    omega
  · change sampleCount P * _ ≤ sampleCount P * _
    apply Nat.mul_le_mul_left (sampleCount P)
    omega

omit [Fintype G] in
/-- The independent complete sampling allowance retains its symbolic width ceiling. -/
public lemma samplingTimeLimit_le_width (P : KnownOrderProblem G) :
    samplingTimeLimit P ≤
      3 + 11 * OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
        (if OrderPreparation.width P / 2 = 0 then 0 else 3) +
        2 * sampleCount P * OrderPreparation.width P := by
  obtain ⟨_single, _cnot, depth⟩ := OrderPreparation.orderPreparation_scalarBounds P
    (OrderExecution.canonicalExpansion P)
  have readout : sampleCount P * OrderExecution.sampleWidth P =
      2 * sampleCount P * OrderPreparation.width P := by
    simp only [OrderExecution.sampleWidth]
    ring
  simp only [samplingTimeLimit, OrderBatch.unitDepth, OrderBatch.programUnitDepth, readout]
  split_ifs <;> omega

/-- Every actual path obeys the scalar native ceilings from the same
independent event budget used by the endpoint's complete solve certificate. -/
public lemma finiteCyclicDLP_code_nativeCounts_le_width (P : KnownOrderProblem G)
    (path : (code P).Path) :
    ResourcePool.count (model := OrderExecution.model P) (.gate .toffoli)
      ((code P).resourcePool path) = 0 ∧
    ResourcePool.count (model := OrderExecution.model P) (.gate .cnot)
      ((code P).resourcePool path) ≤ sampleCount P *
        (6 * OrderPreparation.width P + 4 * (OrderPreparation.width P).choose 2 +
          6 * (OrderPreparation.width P / 2)) ∧
    ResourcePool.count (model := OrderExecution.model P) (.gate .singleQubit)
      ((code P).resourcePool path) ≤ sampleCount P *
        (24 * OrderPreparation.width P + 6 * (OrderPreparation.width P).choose 2) := by
  have bounds := ResourcePool.le_iff_count.mp (code_pool_le P path)
  obtain ⟨cnotWidth, singleWidth⟩ := finiteCyclicDLP_widthResourceBounds P
  have zero := bounds (.gate .toffoli)
  rw [eventBudget_toffoli_count] at zero
  change _ ≤ 0 at zero
  refine ⟨Nat.eq_zero_of_le_zero zero, ?_, ?_⟩
  · have actual := bounds (.gate .cnot)
    rw [eventBudget_cnot_count] at actual
    exact actual.trans cnotWidth
  · have actual := bounds (.gate .singleQubit)
    rw [eventBudget_singleQubit_count] at actual
    exact actual.trans singleWidth

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
