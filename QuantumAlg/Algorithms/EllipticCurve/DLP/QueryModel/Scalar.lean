/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Resources
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Native
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Scalar
import all QuantumAlg.Primitives.QFT.Native.Inverse.Resources

/-!
# Symbolic native coordinates of declared ECDLP sampling

The actual word retains both native preparations, both inverse transforms and
one distinct group-action query. Generic width bounds avoid fixed-instance
bit-table evaluation. Classical context transport introduces no extra events.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem

/-- Every native sampling-word coordinate is independent of any fixed register expansion. -/
public lemma circuit_classical_context_event_count (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (event : Resource.Event (Sampling.executionModel I)) :
    ResourcePool.count event ((circuit I expansion).eventCost BitWord.model .empty) =
      match event with
      | .gate .singleQubit =>
          2 * FiniteCyclicDLP.OrderPreparation.singleQubitCount expansion +
            2 * (FiniteCyclicDLP.orderWidth (problem I) +
              3 * Nat.choose (FiniteCyclicDLP.orderWidth (problem I)) 2)
      | .gate .cnot =>
          2 * FiniteCyclicDLP.OrderPreparation.cnotCount expansion +
            2 * (2 * Nat.choose (FiniteCyclicDLP.orderWidth (problem I)) 2 +
              3 * (FiniteCyclicDLP.orderWidth (problem I) / 2))
      | .gate .toffoli => 0
      | .oracle _ => 1
      | .classicalOperation _ | .classicalQuery _ | .preparation _ | .measurement _ => 0 := by
  rw [UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  cases event with
  | gate coordinate =>
      cases coordinate with
      | toffoli =>
          rw [circuit_eventCost]
          simp only [ResourcePool.count_add]
          simp only [FiniteCyclicDLP.OrderPreparation.Native.circuit_toffoli_count
            (model I) (problem I) expansion]
          simp only [QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
            ResourcePool.count_singleton]
          simp
      | cnot =>
          rw [circuit_eventCost]
          simp only [ResourcePool.count_add]
          simp only [FiniteCyclicDLP.OrderPreparation.Native.circuit_cnot_count
            (model I) (problem I) expansion]
          simp only [QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
            ResourcePool.count_singleton]
          simp
          omega
      | singleQubit =>
          rw [circuit_eventCost]
          simp only [ResourcePool.count_add]
          simp only [FiniteCyclicDLP.OrderPreparation.Native.circuit_singleQubit_count
            (model I) (problem I) expansion]
          simp only [QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
            ResourcePool.count_singleton]
          simp
          omega
  | oracle coordinate =>
      cases coordinate
      exact circuit_query_count I expansion
  | classicalOperation _ => rfl
  | classicalQuery impossible => cases impossible
  | preparation _ => rfl
  | measurement _ => rfl

/-- Generic widths bound both actual known-order peripherals before any instance is fixed. -/
public lemma circuit_preparation_width_bounds (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    FiniteCyclicDLP.OrderPreparation.singleQubitCount expansion ≤
        11 * FiniteCyclicDLP.orderWidth (problem I) ∧
      FiniteCyclicDLP.OrderPreparation.cnotCount expansion ≤
        3 * FiniteCyclicDLP.orderWidth (problem I) ∧
      FiniteCyclicDLP.OrderPreparation.unitDepth expansion ≤
        10 * FiniteCyclicDLP.orderWidth (problem I) + 1 :=
  FiniteCyclicDLP.OrderPreparation.orderPreparation_scalarBounds (problem I) expansion


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
