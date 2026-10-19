/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Both complete first-cycle live-storage peaks

The original bank and exponent/reset cells remain resident beside the seven
actual recovery destinations. Initial preparation and all retention are
included in both peaks. Native checking scratch is the same dimension-indexed
allowance as for a reused complete round; no retry count enlarges it.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma allocation_resident (I : ECDLPInstance E)
    (path : (allocationCode I).Path) :
    (allocationCode I).peakResidentSpace path ≤ (context I).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (initialization_resident_le I path.1).trans ?_
    change _ ≤ (persistentCtx (Sampling.Reuse.context I) (fieldWidth E)
      (scalarWidth I)).residentSpace
    rw [persistentCtx_residentSpace]
    exact fun _ => Nat.le_add_left _ _
  · exact (retainPersistent_resident (model := Sampling.executionModel I)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) path.2).le

private lemma allocation_auxiliary (I : ECDLPInstance E)
    (path : (allocationCode I).Path) :
    (allocationCode I).peakAuxiliarySpace path ≤ (context I).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (initialization_auxiliary_le I path.1).trans ?_
    change _ ≤ (persistentCtx (Sampling.Reuse.context I) (fieldWidth E)
      (scalarWidth I)).auxiliarySpace
    rw [persistentCtx_auxiliarySpace]
    exact fun _ => Nat.le_add_left _ _
  · exact (retainPersistent_auxiliary (model := Sampling.executionModel I)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) path.2).le

/-- Actual initialization and first checked sampling have the full independent resident bound. -/
public lemma ecdlpRecovery_firstRound_resident_le (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (firstRound I expansion nontrivial).Path) :
    (firstRound I expansion nontrivial).peakResidentSpace path ≤ roundResidentBudget I := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (allocation_resident I path.1).trans (fun _ => Nat.le_add_left _ _)
  · exact sampledAttempt_resident_le (Sampling.Reuse.code (allowAllocation := false) I expansion)
      (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path.2

/-- Actual initial allocations and native feedback retain every original auxiliary role. -/
public lemma ecdlpRecovery_firstRound_auxiliary_le (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (firstRound I expansion nontrivial).Path) :
    (firstRound I expansion nontrivial).peakAuxiliarySpace path ≤ roundAuxiliaryBudget I := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (allocation_auxiliary I path.1).trans (fun _ => Nat.le_add_left _ _)
  · exact sampledAttempt_auxiliary_le (Sampling.Reuse.code (allowAllocation := false) I expansion)
      (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) path.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
