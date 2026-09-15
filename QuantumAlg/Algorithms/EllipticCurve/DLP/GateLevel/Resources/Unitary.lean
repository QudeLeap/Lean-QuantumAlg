/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Attempt.Unitary
import all QuantumAlg.Primitives.QFT.Construction

/-!
# Original literal ECDLP unitary resource formulas

The original order-preparation envelope includes both one-term and multi-term
binary expansions. The same preparation, one opaque group query and two inverse
Fourier transforms retain their literal native event and unit-depth formulas.
Actual allocation, finite readout, repeated sampling and recovery consume these
independent formulas at their own execution boundaries.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelResources

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

attribute [local simp] ResourcePool.count_singleton_of_ne
attribute [local simp] Resource.GateLabel.mk.injEq

/-- Independent coordinate envelope for one literal order preparation. -/
def orderPreparationEnvelope {N : Nat} (B : OrderExpansion N) :
    ResourcePool .quantum :=
  ResourcePool.singleton (.gate (.builtin "hadamard")) B.singleQubitBound +
    (ResourcePool.singleton (.gate (.builtin "x")) B.singleQubitBound +
      (ResourcePool.singleton UniformSuperposition.rotationYEvent
          B.singleQubitBound +
        ResourcePool.singleton UniformSuperposition.cnotEvent B.cnotBound))

/-- The literal preparation is bounded by its independent four-coordinate
envelope in both the multi-term and one-term branches. -/
theorem paddedPreparation_eventCost_le_orderPreparationEnvelope
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    (B.paddedPreparation (problem I)).eventCost ≤
      orderPreparationEnvelope B := by
  unfold OrderExpansion.paddedPreparation
  split_ifs with positive
  · rw [FiniteCyclicDLP.Canonical.GateLevelAttempt.paddedPreparation,
      (B.toBinaryExpansion positive).algorithm1CircuitPadded_eventCost]
    simpa only [orderPreparationEnvelope,
      OrderExpansion.toBinaryExpansion_singleQubitBound,
      OrderExpansion.toBinaryExpansion_cnotBound] using
      (B.toBinaryExpansion positive).algorithm1Circuit_eventCost_le_elementaryEnvelope
  · have zero : B.s = 0 := by omega
    rw [UniformSuperposition.withCanonicalFootprint_eventCost,
      UniformSuperposition.padHigh_eventCost,
      WalshHadamard.hadamardLayer_eventCost]
    have firstBound : B.first ≤ B.singleQubitBound := by
      have lastEq := B.last_eq_first_of_s_eq_zero zero
      unfold OrderExpansion.singleQubitBound
      omega
    rw [ResourcePool.le_iff_count]
    intro event
    by_cases hadamard :
        event = (.gate (.builtin "hadamard") : Resource.Event .quantum)
    · subst event
      simp only [WalshHadamard.hadamardEvent, orderPreparationEnvelope,
        ResourcePool.count_add, ResourcePool.count_singleton_self]
      exact firstBound.trans (Nat.le_add_right _ _)
    · have leftZero : ResourcePool.count event
          (ResourcePool.singleton WalshHadamard.hadamardEvent B.first) = 0 := by
        exact ResourcePool.count_singleton_of_ne hadamard B.first
      rw [leftZero]
      exact Nat.zero_le _

/-- Exact event pool of the literal preparation-query-readout circuit. -/
theorem quantumCircuit_eventCost (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    (GateLevelAttempt.quantumCircuit I B A).eventCost =
      ((B.paddedPreparation (problem I)).eventCost +
        (B.paddedPreparation (problem I)).eventCost) +
      (ResourcePool.singleton (uPQEvent I) + (inverseQFTCircuit I).eventCost) := by
  rw [GateLevelAttempt.quantumCircuit, UnitaryCircuit.seq_eventCost,
    UnitaryCircuit.seq_eventCost, GateLevelAttempt.preparationCircuit_eventCost,
    uPQCircuit_eventCost]

private theorem inverseQFTCircuit_eventCost_eq_pair (I : ECDLPInstance E) :
    (inverseQFTCircuit I).eventCost =
      (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost +
        (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost := by
  rw [inverseQFTCircuit, extendWithPoint_eventCost,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventCost,
    UnitaryCircuit.dagger_eventCost]

/-- Locked maximal circuit depth of one literal ECDLP attempt. -/
def attemptDepthLimit (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) : Nat :=
  B.depthBound + 1 +
    (FiniteCyclicDLP.orderWidth (problem I) +
      FiniteCyclicDLP.orderWidth (problem I) *
          (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
        FiniteCyclicDLP.orderWidth (problem I) / 2)

/-- For the preparation circuit based on Algorithm 1 [SV24,
Uniform.tex:640-659], this theorem proves that two parallel copies retain the
depth ceiling proved for one copy. -/
theorem preparationCircuit_evaluatedEventDepth_one_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    (GateLevelAttempt.preparationCircuit I B).evaluatedEventDepth
        (fun _ => 1) ≤ B.depthBound := by
  unfold UnitaryCircuit.evaluatedEventDepth
  rw [GateLevelAttempt.preparationCircuit, extendWithPoint_eventDepth,
    DepthExpr.depthEval_tensor, DepthExpr.depthEval_id, Nat.max_zero,
    GateLevelAttempt.exponentPreparationCircuit,
    FiniteCyclicDLP.Canonical.pairConsecutiveCircuit_eventDepth,
    DepthExpr.depthEval_tensor, Nat.max_self]
  exact B.paddedPreparation_depth_le (problem I)

private theorem inverseQFTCircuit_evaluatedEventDepth_one
    (I : ECDLPInstance E) :
    (inverseQFTCircuit I).evaluatedEventDepth (fun _ => 1) =
      FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) *
            (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
          FiniteCyclicDLP.orderWidth (problem I) / 2 := by
  change DepthExpr.depthEval (fun _ => 1) (inverseQFTCircuit I).eventDepth = _
  rw [inverseQFTCircuit, extendWithPoint_eventDepth,
    FiniteCyclicDLP.ConcreteCircuitAccess.exponentReadoutCircuit,
    FiniteCyclicDLP.ConcreteCircuitAccess.pairConsecutiveCircuit_eventDepth,
    UnitaryCircuit.dagger_eventDepth]
  simp only [DepthExpr.depthEval_tensor, DepthExpr.depthEval_inverse,
    DepthExpr.depthEval_id, Nat.max_zero, Nat.max_self]
  exact QFTCircuit_evaluatedEventDepth_of_one
    (FiniteCyclicDLP.orderWidth (problem I))

/-- The literal preparation-query-readout circuit obeys the locked one-attempt
depth formula under unit event durations. -/
theorem quantumCircuit_evaluatedEventDepth_one_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (A : Access I) :
    (GateLevelAttempt.quantumCircuit I B A).evaluatedEventDepth
        (fun _ => 1) ≤ attemptDepthLimit I B := by
  rw [GateLevelAttempt.quantumCircuit, UnitaryCircuit.evaluatedEventDepth_seq,
    UnitaryCircuit.evaluatedEventDepth_seq,
    inverseQFTCircuit_evaluatedEventDepth_one]
  have preparationBound := preparationCircuit_evaluatedEventDepth_one_le I B
  change
    (GateLevelAttempt.preparationCircuit I B).evaluatedEventDepth (fun _ => 1) +
        (1 + (FiniteCyclicDLP.orderWidth (problem I) +
          FiniteCyclicDLP.orderWidth (problem I) *
              (FiniteCyclicDLP.orderWidth (problem I) - 1) / 2 +
            FiniteCyclicDLP.orderWidth (problem I) / 2)) ≤ _
  unfold attemptDepthLimit
  omega

end

end GateLevelResources
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
