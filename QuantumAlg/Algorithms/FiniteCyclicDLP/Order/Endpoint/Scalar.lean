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
The same complete batch has one certified sampling cycle and a separately
accounted classical recovery tail. Native group systems retain their actual
dimension rather than being assigned a binary encoding.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The actual group system retains the ambient group's cardinality as its
dimension. No binary encoding or subgroup-generation premise is needed. -/
public theorem finiteCyclicDLP_groupDimension_eq_card :
    (OrderOracle.workspaceDimension G).val = Fintype.card G := rfl

/-- When the advertised generator covers the whole group, its native system
has the known order as its dimension. The original algorithm also admits
ambient groups without this supplementary premise. -/
public theorem finiteCyclicDLP_groupDimension_eq_order (P : KnownOrderProblem G)
    (covers : ∀ target : G, target ∈ Subgroup.zpowers P.generator) :
    (OrderOracle.workspaceDimension G).val = P.order := by
  classical
  change Fintype.card G = P.order
  rw [P.order_eq_orderOf]
  simpa only [Nat.card_eq_fintype_card] using
    (orderOf_eq_card_of_forall_mem_zpowers covers).symm

/-- Independent native and maximum-cycle ceilings use only the symbolic
register width and the original retry count. -/
public theorem finiteCyclicDLP_widthResourceBounds (P : KnownOrderProblem G) :
    (publicCoordinates P).cnotGates ≤ sampleCount P *
      (6 * OrderPreparation.width P + 4 * (OrderPreparation.width P).choose 2 +
        6 * (OrderPreparation.width P / 2)) ∧
    (publicCoordinates P).singleQubitGates ≤ sampleCount P *
      (24 * OrderPreparation.width P + 6 * (OrderPreparation.width P).choose 2) ∧
    (publicCoordinates P).maximumCompleteCycleDepth ≤
      3 + 11 * OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
        3 * (OrderPreparation.width P / 2) +
        2 * sampleCount P * OrderPreparation.width P := by
  obtain ⟨single, cnot, depth⟩ := OrderPreparation.orderPreparation_scalarBounds P
    (OrderExecution.canonicalExpansion P)
  constructor
  · change sampleCount P * _ ≤ sampleCount P * _
    apply Nat.mul_le_mul_left (sampleCount P)
    omega
  constructor
  · change sampleCount P * _ ≤ sampleCount P * _
    apply Nat.mul_le_mul_left (sampleCount P)
    omega
  · have readout : sampleCount P * OrderExecution.sampleWidth P =
        2 * sampleCount P * OrderPreparation.width P := by
      simp only [OrderExecution.sampleWidth]
      ring
    simp only [publicCoordinates, completeCycleDepthLimit, OrderBatch.unitDepth,
      OrderBatch.programUnitDepth, readout]
    split_ifs <;> omega

/-- Every actual path obeys the scalar native ceilings from the same
independent event budget used by the endpoint's complete solve certificate. -/
public theorem finiteCyclicDLP_code_nativeCounts_le_width (P : KnownOrderProblem G)
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
  obtain ⟨cnotWidth, singleWidth, _⟩ := finiteCyclicDLP_widthResourceBounds P
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

/-- The actual complete sampling cycle satisfies the width ceiling; the
full classical recovery remains separately charged in whole-run depth. -/
public theorem finiteCyclicDLP_code_cycleDepth_le_width (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) (path : (code P).Path) :
    (codeCycleSchedule P secret).maximumCycleDepth (fun _ => 1) path ≤
      3 + 11 * OrderPreparation.width P + 5 * (OrderPreparation.width P).choose 2 +
        3 * (OrderPreparation.width P / 2) +
        2 * sampleCount P * OrderPreparation.width P :=
  (code_maximumCycleDepth_le_publicCoordinates P secret path).trans
    (finiteCyclicDLP_widthResourceBounds P).2.2

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
