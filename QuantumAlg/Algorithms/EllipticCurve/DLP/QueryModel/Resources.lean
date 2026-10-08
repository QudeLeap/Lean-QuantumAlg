/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Circuit
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Circuit
public import QuantumAlg.Primitives.QFT.Native.Inverse.Resources
public import QuantumAlg.Primitives.QFT.Native.Inverse.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Intrinsic resources of the actual declared ECDLP sampling word

The query coordinate is distinct from native point arithmetic. Parallel
peripherals retain both event ledgers and the maximum of their branch depths.
These are sampling-word observations, not a full recovery/retry contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local implicit_reducible] problem

/-- The complete ledger is obtained from both actual native peripherals and one query. -/
public theorem circuit_eventCost (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (circuit I A expansion).eventCost =
      ((FiniteCyclicDLP.OrderPreparation.Native.circuit (model I A)
          (problem I) expansion).eventCost +
        (FiniteCyclicDLP.OrderPreparation.Native.circuit (model I A)
          (problem I) expansion).eventCost) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model (model I A))
        (.oracle Coordinate.groupAction) +
      ((QuantumFourierTransform.Native.inverseCircuit (model I A)
          (FiniteCyclicDLP.orderWidth (problem I))).eventCost +
        (QuantumFourierTransform.Native.inverseCircuit (model I A)
          (FiniteCyclicDLP.orderWidth (problem I))).eventCost) := by
  rw [circuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    preparations, inverseQFTs, UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventCost,
    UnitaryCircuit.parallelBinary_eventCost, UnitaryCircuit.parallelBinary_eventCost,
    oracleLayer, UnitaryCircuit.query_eventCost]
  rfl

/-- Exactly one ordinary group-action query is executed for every positive order. -/
public theorem circuit_query_count (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    ResourcePool.count (model := .quantum AlgorithmGate.model (model I A))
      (.oracle Coordinate.groupAction) (circuit I A expansion).eventCost = 1 := by
  rw [circuit_eventCost]
  simp only [ResourcePool.count_add,
    QuantumFourierTransform.Native.qftNative_inverseCircuit_event_count,
    ResourcePool.count_singleton_self]
  rw [FiniteCyclicDLP.OrderPreparation.Native.circuit_oracle_count
    (model I A) (problem I) expansion Coordinate.groupAction]
  simp

/-- Exact parallel-peripheral depth plus the one actual query step. -/
public theorem circuit_unit_depth (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder) :
    (circuit I A expansion).evaluatedEventDepth (fun _ => 1) =
      FiniteCyclicDLP.OrderPreparation.unitDepth expansion + 1 +
        (FiniteCyclicDLP.orderWidth (problem I) +
          5 * Nat.choose (FiniteCyclicDLP.orderWidth (problem I)) 2 +
          3 * (FiniteCyclicDLP.orderWidth (problem I) / 2)) := by
  rw [circuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq,
    preparations, inverseQFTs,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth,
    UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth,
    UnitaryCircuit.parallelBinary_evaluatedEventDepth,
    UnitaryCircuit.parallelBinary_evaluatedEventDepth, Nat.max_self, Nat.max_self,
    FiniteCyclicDLP.OrderPreparation.Native.circuit_unit_depth]
  have Fourier := QuantumFourierTransform.Native.qftNative_inverseCircuit_unit_depth
    (model I A) (FiniteCyclicDLP.orderWidth (problem I))
  rw [Fourier]
  rfl

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel
