/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.ResourceProjections.Unitary
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Access.Concrete

/-!
# Pure resources of the intrinsic-layout ECDLP unitary experiment

The original exact range preparations, opaque group-action query and two
inverse QFTs determine these literal event projections. The retained duration
assigns one layer to gates and quantum queries and zero to other event kinds.
These statements concern the unitary experiment and its original analytical
range-preparation leaves. Allocation, measured reset and recovery are charged
by their actual execution owners.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

namespace Runtime.Run

/-- Circuit-depth interpretation used by the public ECDLP endpoint. -/
def depthAssignment : Resource.Event .quantum → Nat
  | .gate _ => 1
  | .quantumSubroutine _ => 1
  | .preparation _ => 0
  | .measurement _ => 0
  | .classicalOperation _ => 0
  | .classicalSubroutine _ => 0

end Runtime.Run

namespace Resources.Classical

/-- The exact range-preparation circuit contains only gate events. -/
theorem preparationCircuit_classicalOperationCard_zero (I : ECDLPInstance E) :
    FiniteCyclicDLP.Canonical.classicalOperationCard
      (preparationCircuit I).eventCost = 0 := by
  rw [preparationCircuit, extendWithPoint_eventCost]
  rw [FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    FiniteCyclicDLP.Canonical.classicalOperationCard_add]
  change
    FiniteCyclicDLP.Canonical.classicalOperationCard
        (ResourcePool.singleton
          (.gate Gate.finiteCyclicRangePreparationGateLabel)) +
      FiniteCyclicDLP.Canonical.classicalOperationCard
        (ResourcePool.singleton
          (.gate Gate.finiteCyclicRangePreparationGateLabel)) = 0
  simp [FiniteCyclicDLP.Canonical.classicalOperationCard_singleton_nonClassical]

/-- The structural inverse QFT readout contains only gate events. -/
theorem inverseQFTCircuit_classicalOperationCard_zero (I : ECDLPInstance E) :
    FiniteCyclicDLP.Canonical.classicalOperationCard
      (inverseQFTCircuit I).eventCost = 0 := by
  rw [inverseQFTCircuit, extendWithPoint_eventCost]
  rw [FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    FiniteCyclicDLP.Canonical.classicalOperationCard_add]
  change
    FiniteCyclicDLP.Canonical.classicalOperationCard
        (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost +
      FiniteCyclicDLP.Canonical.classicalOperationCard
        (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost = 0
  rw [FiniteCyclicDLP.Canonical.qftCircuit_classicalOperationCard_zero]

/-- The opaque group-action occurrence is a quantum-subroutine coordinate,
not a literal classical operation. -/
theorem uPQCircuit_classicalOperationCard_zero
    (I : ECDLPInstance E) (A : Access I) :
    FiniteCyclicDLP.Canonical.classicalOperationCard
      (uPQCircuit I A).eventCost = 0 := by
  rw [uPQCircuit_eventCost]
  exact FiniteCyclicDLP.Canonical.classicalOperationCard_singleton_nonClassical
    (uPQEvent I) (by
      intro operation equality
      cases equality) 1

end Resources.Classical

namespace Resources.Depth

/-- Closed depth of one real prepare-query-readout attempt. -/
def depthPerAttempt (I : ECDLPInstance E) : Nat :=
  2 + FiniteCyclicDLP.orderWidth (problem I) +
    FiniteCyclicDLP.orderWidth (problem I) *
        (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
      FiniteCyclicDLP.orderWidth (problem I) / 2

/-- Exact unit-depth formula for a structural QFT in the strict event view. -/
theorem qftCircuit_evaluatedEventDepth (width : Nat) :
    (QFTCircuit width).evaluatedEventDepth Runtime.Run.depthAssignment =
      width + width * (width - 1) / 2 + width / 2 := by
  exact QFTCircuit_evaluatedEventDepth width Runtime.Run.depthAssignment
    rfl rfl rfl

/-- The two range preparations execute in parallel and occupy one layer. -/
theorem preparationCircuit_evaluatedEventDepth (I : ECDLPInstance E) :
    (preparationCircuit I).evaluatedEventDepth Runtime.Run.depthAssignment = 1 := by
  simp [preparationCircuit, extendWithPoint_eventDepth,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventDepth,
    FiniteCyclicDLP.rangePreparationCircuit_eventDepth,
    FiniteCyclicDLP.rangePreparationEvent,
    UnitaryCircuit.evaluatedEventDepth, Runtime.Run.depthAssignment]

/-- The opaque `U_{P,Q}` query occupies exactly one layer. -/
theorem uPQCircuit_evaluatedEventDepth
    (I : ECDLPInstance E) (A : Access I) :
    (uPQCircuit I A).evaluatedEventDepth Runtime.Run.depthAssignment = 1 := by
  rfl

/-- Parallel inverse QFTs have the depth of one structural QFT. -/
theorem inverseQFTCircuit_evaluatedEventDepth (I : ECDLPInstance E) :
    (inverseQFTCircuit I).evaluatedEventDepth Runtime.Run.depthAssignment =
      FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) *
            (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
          FiniteCyclicDLP.orderWidth (problem I) / 2 := by
  change DepthExpr.depthEval Runtime.Run.depthAssignment
    (inverseQFTCircuit I).eventDepth = _
  rw [inverseQFTCircuit, extendWithPoint_eventDepth,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventDepth]
  simp only [DepthExpr.depthEval_tensor, DepthExpr.depthEval_id,
    Nat.max_zero, Nat.max_self]
  exact qftCircuit_evaluatedEventDepth _

/-- Exact maximal depth of one real intrinsic-layout quantum circuit. -/
theorem quantumCircuit_evaluatedEventDepth
    (I : ECDLPInstance E) (A : Access I) :
    (quantumCircuit I A).evaluatedEventDepth Runtime.Run.depthAssignment =
      depthPerAttempt I := by
  change
    (preparationCircuit I).evaluatedEventDepth Runtime.Run.depthAssignment +
      ((uPQCircuit I A).evaluatedEventDepth Runtime.Run.depthAssignment +
        (inverseQFTCircuit I).evaluatedEventDepth
          Runtime.Run.depthAssignment) = _
  rw [preparationCircuit_evaluatedEventDepth,
    uPQCircuit_evaluatedEventDepth,
    inverseQFTCircuit_evaluatedEventDepth]
  unfold depthPerAttempt
  omega

/-- The shared concrete-circuit spine contains precisely the intrinsic-layout
quantum circuit above. -/
theorem circuitAccess_fullCircuit_evaluatedEventDepth
    (I : ECDLPInstance E) (A : Access I) :
    ((circuitAccess I A).fullCircuit).evaluatedEventDepth
        Runtime.Run.depthAssignment = depthPerAttempt I := by
  change (quantumCircuit I A).evaluatedEventDepth
    Runtime.Run.depthAssignment = depthPerAttempt I
  exact quantumCircuit_evaluatedEventDepth I A

end Resources.Depth

namespace Resources.Quantum

open FiniteCyclicDLP.Canonical

/-- Literal gate leaves in one real ECDLP attempt: two exact range-preparation
leaves and two structural inverse QFTs. -/
def gateCountPerAttempt (I : ECDLPInstance E) : Nat :=
  2 + 2 * (FiniteCyclicDLP.orderWidth (problem I) +
    (FiniteCyclicDLP.orderWidth (problem I)).choose 2 +
      FiniteCyclicDLP.orderWidth (problem I) / 2)

/-- Extending an exponent-register circuit by the identity point register does
not change its literal gate projection. -/
theorem elementaryGateCard_extendWithPoint
    (I : ECDLPInstance E)
    (body : UnitaryCircuit (Qubits
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))))
    (physical : body.physical_idx = List.range
      (FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I))) :
    elementaryGateCard (extendWithPoint I body physical).eventCost =
      elementaryGateCard body.eventCost := by
  rw [extendWithPoint_eventCost]

/-- The two exact range-preparation leaves contribute two literal gate events. -/
theorem preparationCircuit_elementaryGateCard (I : ECDLPInstance E) :
    elementaryGateCard (preparationCircuit I).eventCost = 2 := by
  rw [preparationCircuit, elementaryGateCard_extendWithPoint]
  rw [FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    elementaryGateCard_add]
  change
    elementaryGateCard (ResourcePool.singleton
        (.gate Gate.finiteCyclicRangePreparationGateLabel)) +
      elementaryGateCard (ResourcePool.singleton
        (.gate Gate.finiteCyclicRangePreparationGateLabel)) = 2
  simp

/-- The two inverse QFTs contribute the exact structural QFT gate formula. -/
theorem inverseQFTCircuit_elementaryGateCard (I : ECDLPInstance E) :
    elementaryGateCard (inverseQFTCircuit I).eventCost =
      2 * (FiniteCyclicDLP.orderWidth (problem I) +
        (FiniteCyclicDLP.orderWidth (problem I)).choose 2 +
          FiniteCyclicDLP.orderWidth (problem I) / 2) := by
  rw [inverseQFTCircuit, elementaryGateCard_extendWithPoint]
  rw [FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    elementaryGateCard_add]
  change
    elementaryGateCard (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost +
      elementaryGateCard (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost = _
  rw [qftCircuit_elementaryGateCard]
  omega

/-- The opaque query leaf is not classified as a literal elementary gate. -/
theorem uPQCircuit_elementaryGateCard_zero
    (I : ECDLPInstance E) (A : Access I) :
    elementaryGateCard (uPQCircuit I A).eventCost = 0 := by
  rw [uPQCircuit_eventCost]
  exact elementaryGateCard_singleton_nonGate (uPQEvent I) (by
    intro label equality
    cases equality) 1

/-- Exact literal gate count of the real quantum circuit in one attempt. -/
theorem quantumCircuit_elementaryGateCard
    (I : ECDLPInstance E) (A : Access I) :
    elementaryGateCard (quantumCircuit I A).eventCost = gateCountPerAttempt I := by
  rw [quantumCircuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    elementaryGateCard_add, elementaryGateCard_add,
    preparationCircuit_elementaryGateCard,
    uPQCircuit_elementaryGateCard_zero,
    inverseQFTCircuit_elementaryGateCard]
  simp [gateCountPerAttempt]

/-- Exact range preparation contains no opaque query event. -/
theorem preparationCircuit_uPQEvent_count_zero
    (I : ECDLPInstance E) :
    ResourcePool.count (uPQEvent I) (preparationCircuit I).eventCost = 0 := by
  simp [preparationCircuit, extendWithPoint_eventCost,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentPreparationCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    FiniteCyclicDLP.rangePreparationCircuit,
    FiniteCyclicDLP.rangePreparationLeaf,
    Gate.finiteCyclicRangePreparationLeafAt, UnitaryLeaf.gate_event,
    uPQEvent, ResourcePool.count, ResourcePool.singleton]

/-- Structural inverse QFT readout contains no opaque query event. -/
theorem inverseQFTCircuit_uPQEvent_count_zero
    (I : ECDLPInstance E) :
    ResourcePool.count (uPQEvent I) (inverseQFTCircuit I).eventCost = 0 := by
  simp [inverseQFTCircuit, extendWithPoint_eventCost,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    QFTCircuit_eventCost_eq, uPQEvent, ResourcePool.count,
    ResourcePool.singleton]

/-- The real circuit contains exactly one `U_{P,Q}` query. -/
theorem quantumCircuit_uPQEvent_count
    (I : ECDLPInstance E) (A : Access I) :
    ResourcePool.count (uPQEvent I) (quantumCircuit I A).eventCost = 1 := by
  rw [quantumCircuit, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    ResourcePool.count_add, ResourcePool.count_add,
    uPQCircuit_eventCost, preparationCircuit_uPQEvent_count_zero,
    inverseQFTCircuit_uPQEvent_count_zero]
  simp

end Resources.Quantum

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
