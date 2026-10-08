/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
public import QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Preparation
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete allocation-to-recovery resources of the actual declared ECDLP run

The initial physical zero preparation and all retained allocations precede
the same real finite recovery tail. Both complete live-storage peaks are
bounded by the tail allowance, independently of the prescribed round count.
Initial preparation is charged in addition to every sampling/checking round
and the final actual pack. These are full native-dimensional inventories;
the scalar endpoint allowance is a later projection of this same run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every actually prepared bank system is charged once before finite physical reuse. -/
public def initializationBudget (I : ECDLPInstance E) (A : Access I) :
    ResourcePool (Sampling.executionModel I A) :=
  ZeroPreparation.eventCost AlgorithmGate.model (model I A) (layout I) BitWord.model .empty

/-- The initial preparation and complete actual tail share one event allowance. -/
public def eventBudget (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    ResourcePool (Sampling.executionModel I A) :=
  initializationBudget I A + tailEventBudget I A expansion nontrivial count

private theorem initialization_events (I : ECDLPInstance E) (A : Access I)
    (path : (Sampling.Reuse.initialCode I A).Path) :
    (Sampling.Reuse.initialCode I A).resourcePool path = initializationBudget I A := by
  simp only [Sampling.Reuse.initialCode, Sampling.initialCode, Circuit.resourcePool,
    Circuit.eventTrace, Sampling.allocation_trace, ResourcePool.ofList_append,
    ResourcePool.ofList_nil, add_zero, Sampling.preparation_pool]
  rfl

private theorem initialization_resident_le (I : ECDLPInstance E) (A : Access I)
    (path : (Sampling.Reuse.initialCode I A).Path) :
    (Sampling.Reuse.initialCode I A).peakResidentSpace path ≤
      (Sampling.Reuse.context I).residentSpace := by
  have bank : (Sampling.preparationCode I A).peakResidentSpace path.1.1 =
      (Sampling.bankContext I).residentSpace :=
    Circuit.prepare_peakResidentSpace (gates := AlgorithmGate.model)
    (oracles := model I A) (operations := BitWord.model) (classicalOracles := .empty)
    (Sampling.pre I) (Sampling.pre I).canonicalFreshKey (layout I)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.pre I))
    (Sampling.bankDisjoint I) path.1.1
  have cells := MeasurementCells.allocate_peakResidentSpace
    (model := Sampling.executionModel I A) (Sampling.bankContext I) 2 (Sampling.sampleWidth I)
    path.1.2
  have allocated : (Sampling.initialCode I A).peakResidentSpace path.1 ≤
      (Sampling.post I).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ cells)
    exact bank.le.trans (MeasurementCells.context_residentSpace_mono (Sampling.bankContext I) 2
      (Nat.zero_le (Sampling.sampleWidth I)))
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact allocated.trans (by
      rw [Sampling.Reuse.ecdlpReuse_context_resident]
      exact fun _ => Nat.le_add_left _ _)
  · exact (Circuit.peakResidentSpace_retain (model := Sampling.executionModel I A)
      (Sampling.post I).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I)) path.2).le

private theorem initialization_auxiliary_le (I : ECDLPInstance E) (A : Access I)
    (path : (Sampling.Reuse.initialCode I A).Path) :
    (Sampling.Reuse.initialCode I A).peakAuxiliarySpace path ≤
      (Sampling.Reuse.context I).auxiliarySpace := by
  have bank : (Sampling.preparationCode I A).peakAuxiliarySpace path.1.1 =
      (Sampling.bankContext I).auxiliarySpace :=
    Circuit.prepare_peakAuxiliarySpace (gates := AlgorithmGate.model)
    (oracles := model I A) (operations := BitWord.model) (classicalOracles := .empty)
    (Sampling.pre I) (Sampling.pre I).canonicalFreshKey (layout I)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.pre I))
    (Sampling.bankDisjoint I) path.1.1
  have cells := MeasurementCells.allocate_peakAuxiliarySpace
    (model := Sampling.executionModel I A) (Sampling.bankContext I) 2 (Sampling.sampleWidth I)
    path.1.2
  have allocated : (Sampling.initialCode I A).peakAuxiliarySpace path.1 ≤
      (Sampling.post I).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ cells)
    exact bank.le.trans (MeasurementCells.context_auxiliarySpace_mono (Sampling.bankContext I) 2
      (Nat.zero_le (Sampling.sampleWidth I)))
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact allocated.trans (by
      rw [Sampling.Reuse.ecdlpReuse_context_auxiliary]
      exact fun _ => Nat.le_add_left _ _)
  · exact (Circuit.peakAuxiliarySpace_retain (model := Sampling.executionModel I A)
      (Sampling.post I).canonicalFreshKey (.finite 2)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I)) path.2).le

/-- Every event of the same complete actual run is charged, including count zero. -/
public theorem ecdlpRecovery_code_events_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (code I A expansion nontrivial count).Path) :
    (code I A expansion nontrivial count).resourcePool path ≤
      eventBudget I A expansion nontrivial count := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (initialization_events I A path.1).le
    (ecdlpRecovery_tail_events_le I A expansion nontrivial count path.2)

/-- The full run's resident peak includes the initial allocations and all finite rounds. -/
public theorem ecdlpRecovery_code_resident_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (code I A expansion nontrivial count).Path) :
    (code I A expansion nontrivial count).peakResidentSpace path ≤ tailResidentBudget I := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (initialization_resident_le I A path.1).trans (fun _ => Nat.le_add_left _ _)
  · exact ecdlpRecovery_tail_resident_le I A expansion nontrivial count path.2

/-- The full auxiliary peak retains all original roles throughout allocation and reuse. -/
public theorem ecdlpRecovery_code_auxiliary_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (path : (code I A expansion nontrivial count).Path) :
    (code I A expansion nontrivial count).peakAuxiliarySpace path ≤ tailAuxiliaryBudget I := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (initialization_auxiliary_le I A path.1).trans (fun _ => Nat.le_add_left _ _)
  · exact ecdlpRecovery_tail_auxiliary_le I A expansion nontrivial count path.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
