/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Scalar
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Scalar
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Initialization
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Primitives.ZReset.Resources

/-!
# Actual initialized-word and complete double-reset coordinates

The transported native word pays its actual infinity-tag X. Both complete
physical bank resets and every exponent measurement remain in the per-round
allowance. All widths and native preparation data remain symbolic.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] Layout.pointWidth

private lemma initialized_word_pool (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (Sampling.Reuse.nativeProgram I expansion).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (model I))
        (.gate .singleQubit) + (circuit I expansion).eventCost := by
  rw [Sampling.Reuse.nativeProgram, Execution.unitaryOfEqualWires_cost,
    UnitaryCircuit.seq_eventCost, initializer,
    UnitaryCircuit.unitaryCircuit_onBinarySuffix_eventCost, pointInitializer]
  rfl

/-- The actual infinity-tag X is paid beside the unchanged transported query word. -/
public lemma initialized_word_count (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (event : Resource.Event (Sampling.executionModel I)) :
    ResourcePool.count event
        ((Sampling.Reuse.nativeProgram I expansion).eventCost BitWord.model .empty) =
      (if event = .gate .singleQubit then 1 else 0) +
        ResourcePool.count event ((circuit I expansion).eventCost BitWord.model .empty) := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event <;> simp [initialized_word_pool, ResourcePool.count_add,
    ResourcePool.count_singleton, eq_comm]

/-- Both full-bank resets and all exponent reads have independent symbolic coordinates. -/
public lemma reused_sampling_budget_count (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (event : Resource.Event (Sampling.executionModel I)) :
    ResourcePool.count event (Sampling.Reuse.eventBudget I expansion) =
      2 * (Sampling.Reuse.context I).systemCount *
          ((if event = .gate .singleQubit then 1 else 0) +
            (if event = .measurement (2 : ℕ+) then 1 else 0)) +
        (if event = .gate .singleQubit then 1 else 0) +
        ResourcePool.count event ((circuit I expansion).eventCost BitWord.model .empty) +
        Sampling.sampleWidth I * (if event = .measurement (2 : ℕ+) then 1 else 0) := by
  simp only [Sampling.Reuse.eventBudget, ResourcePool.count_add,
    ZReset.Bank.envelope, ZReset.eventEnvelope, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, initialized_word_count]
  simp only [eq_comm]
  ring


private lemma bank_systemCount (I : ECDLPInstance E) :
    (Sampling.Reuse.context I).systemCount = Layout.totalQubits I := by
  have same := congrArg List.length (Sampling.Reuse.ecdlpReuse_sourceWires I)
  simpa only [QuantumLayout.wires_length] using same.symm

/-- A width-only pool dominates the unchanged actual sampling allowance. -/
public lemma reused_sampling_scalar_pool_le (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    Sampling.Reuse.eventBudget I expansion ≤
      ResourcePool.singleton (model := Sampling.executionModel I) (.gate .singleQubit)
        (2 * Layout.totalQubits I + 1 + 22 * FiniteCyclicDLP.orderWidth (problem I) +
          2 * (FiniteCyclicDLP.orderWidth (problem I) +
            3 * Nat.choose (FiniteCyclicDLP.orderWidth (problem I)) 2)) +
      ResourcePool.singleton (model := Sampling.executionModel I) (.gate .cnot)
        (6 * FiniteCyclicDLP.orderWidth (problem I) +
          2 * (2 * Nat.choose (FiniteCyclicDLP.orderWidth (problem I)) 2 +
            3 * (FiniteCyclicDLP.orderWidth (problem I) / 2))) +
      ResourcePool.singleton (model := Sampling.executionModel I)
        (.oracle Coordinate.groupAction) +
      ResourcePool.singleton (model := Sampling.executionModel I) (.measurement (2 : ℕ+))
        (2 * Layout.totalQubits I + 2 * FiniteCyclicDLP.orderWidth (problem I)) := by
  have preparation := circuit_preparation_width_bounds I expansion
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [reused_sampling_budget_count, bank_systemCount, circuit_classical_context_event_count]
  cases event with
  | gate coordinate =>
      cases coordinate <;>
        simp [ResourcePool.count_add, ResourcePool.count_singleton, Sampling.sampleWidth] <;>
        omega
  | oracle coordinate =>
      cases coordinate
      simp [ResourcePool.count_add, ResourcePool.count_singleton]
  | measurement dimension =>
      by_cases same : dimension = (2 : ℕ+)
      · subst dimension
        simp [ResourcePool.count_add, ResourcePool.count_singleton, Sampling.sampleWidth]
        omega
      · simp [ResourcePool.count_add, ResourcePool.count_singleton, same, Ne.symm same]
  | preparation dimension => simp [ResourcePool.count_add, ResourcePool.count_singleton]
  | classicalOperation label => simp [ResourcePool.count_add, ResourcePool.count_singleton]
  | classicalQuery impossible => cases impossible


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
