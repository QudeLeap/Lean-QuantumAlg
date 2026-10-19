/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
public import QuantumAlg.Util.Nat.ChooseTwo
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Resources
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Resources

/-!
# Width formulas for actual sequential binary DLP sampling

The former native preparation and inverse-QFT counts remain unchanged.
Each terminal physical reset adds at most one X on every actual bank qubit.
The result is derived from the same full sampler's event allowance; no
arithmetic or oracle implementation is changed [Sho95, source.tex:1713-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

private lemma preparation_gate_zero (P : KnownOrderProblem G)
    (coordinate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := model P) (.gate coordinate)
      (ZeroPreparation.eventCost AlgorithmGate.model (Binary.Oracle.model P)
        (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)) = 0 := by
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.count, ResourcePool.ofList]

private lemma preparation_query_zero (P : KnownOrderProblem G) :
    ResourcePool.count (model := model P) (.oracle .ux)
      (ZeroPreparation.eventCost AlgorithmGate.model (Binary.Oracle.model P)
        (Binary.Oracle.layout P) BitWord.model (ClassicalFiniteGroupOracle.model G)) = 0 := by
  simp [ZeroPreparation.eventCost, ZeroPreparation.eventTrace,
    ResourcePool.count, ResourcePool.ofList]

/-- Reset contains no CNOT, so its physical realization leaves the previous CNOT formula intact. -/
public lemma reusableDLP_eventBudget_cnot_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := model P) (.gate .cnot) (eventBudget P count expansion) =
      count * (2 * OrderPreparation.cnotCount expansion +
        2 * (2 * (OrderPreparation.width P).choose 2 +
          3 * (OrderPreparation.width P / 2))) := by
  unfold eventBudget roundEventBudget
  rw [ResourcePool.count_add, preparation_gate_zero, ResourcePool.count_scale,
    ResourcePool.count_add, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  simp [Binary.Circuit.binaryCircuit_circuit_cnot_count,
    ZReset.Bank.envelope, ZReset.eventEnvelope]

/-- The reset allowance adds one possible native X per actual qubit per round. -/
public lemma reusableDLP_eventBudget_singleQubit_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := model P) (.gate .singleQubit)
      (eventBudget P count expansion) =
      count * (2 * OrderPreparation.singleQubitCount expansion +
        2 * (OrderPreparation.width P + 3 * (OrderPreparation.width P).choose 2) +
        bankWidth P) := by
  unfold eventBudget roundEventBudget
  rw [ResourcePool.count_add, preparation_gate_zero, ResourcePool.count_scale,
    ResourcePool.count_add, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  simp [Binary.Circuit.binaryCircuit_circuit_singleQubit_count,
    ZReset.Bank.envelope, ZReset.eventEnvelope]

/-- All rounds, including the last, use the same one declared quantum query. -/
public lemma eventBudget_query_count (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := model P) (.oracle .ux) (eventBudget P count expansion) =
      count := by
  unfold eventBudget roundEventBudget
  rw [ResourcePool.count_add, preparation_query_zero, ResourcePool.count_scale,
    ResourcePool.count_add, ResourcePool.count_add,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  simp [Binary.Circuit.binaryCircuit_circuit_ux_count,
    ZReset.Bank.envelope, ZReset.eventEnvelope]

private lemma pairs_square (width : Nat) : 2 * width.choose 2 + width = width ^ 2 := by
  rw [ChooseTwo.twice_choose_two]
  cases width with
  | zero => rfl
  | succ width => simp only [Nat.add_sub_cancel]; ring

/-- The complete sampler's CNOT ceiling in the reviewed polynomial form. -/
public lemma eventBudget_cnot_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := model P) (.gate .cnot) (eventBudget P count expansion) ≤
      count * (2 * (OrderPreparation.width P) ^ 2 + 4 * OrderPreparation.width P +
        6 * (OrderPreparation.width P / 2)) := by
  rw [reusableDLP_eventBudget_cnot_count]
  apply Nat.mul_le_mul_left
  obtain ⟨_, cnot, _⟩ := OrderPreparation.orderPreparation_scalarBounds P expansion
  have pairs := pairs_square (OrderPreparation.width P)
  omega

/-- The single-qubit ceiling includes every actual possible terminal reset X. -/
public lemma eventBudget_singleQubit_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) :
    ResourcePool.count (model := model P) (.gate .singleQubit)
      (eventBudget P count expansion) ≤
      count * (3 * (OrderPreparation.width P) ^ 2 + 23 * OrderPreparation.width P +
        Binary.groupWidth P) := by
  rw [reusableDLP_eventBudget_singleQubit_count]
  apply Nat.mul_le_mul_left
  obtain ⟨single, _, _⟩ := OrderPreparation.orderPreparation_scalarBounds P expansion
  have pairs := pairs_square (OrderPreparation.width P)
  unfold bankWidth sampleWidth
  omega

omit [Fintype G] in
/-- The first round's prefix allowance and every complete round obey the displayed depth formula. -/
public lemma round_depth_scalar (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    1 + roundUnitDepth P expansion ≤
      (5 * (OrderPreparation.width P) ^ 2 + 29 * OrderPreparation.width P) / 2 +
        2 * Binary.groupWidth P + 3 * (OrderPreparation.width P / 2) + 3 := by
  obtain ⟨_, _, depth⟩ := OrderPreparation.orderPreparation_scalarBounds P expansion
  have pairs := pairs_square (OrderPreparation.width P)
  have numerator :
      5 * (OrderPreparation.width P) ^ 2 + 29 * OrderPreparation.width P =
        2 * (5 * (OrderPreparation.width P).choose 2 + 17 * OrderPreparation.width P) := by
    omega
  rw [numerator, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  unfold roundUnitDepth bankWidth sampleWidth
  split_ifs <;> omega

/-- These bounds apply to every path of the same physical sampler, including every reset. -/
public lemma code_nativeCounts_le (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order) (path : (code P count expansion).Path) :
    ResourcePool.count (model := model P) (.gate .cnot)
        ((code P count expansion).resourcePool path) ≤
      count * (2 * (OrderPreparation.width P) ^ 2 + 4 * OrderPreparation.width P +
        6 * (OrderPreparation.width P / 2)) ∧
    ResourcePool.count (model := model P) (.gate .singleQubit)
        ((code P count expansion).resourcePool path) ≤
      count * (3 * (OrderPreparation.width P) ^ 2 + 23 * OrderPreparation.width P +
        Binary.groupWidth P) ∧
    ResourcePool.count (model := model P) (.oracle .ux)
        ((code P count expansion).resourcePool path) ≤ count := by
  have actual := ResourcePool.le_iff_count.mp (reusableDLP_code_events_le P count expansion path)
  refine ⟨(actual (.gate .cnot)).trans (eventBudget_cnot_le P count expansion),
    (actual (.gate .singleQubit)).trans (eventBudget_singleQubit_le P count expansion), ?_⟩
  exact (actual (.oracle .ux)).trans_eq (eventBudget_query_count P count expansion)

end

end QuantumAlg.FiniteCyclicDLP.Reusable
