/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Solves
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Core.Execution.CycleSchedule.Bounds
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# The original positive finite ECDLP run has actual complete cycles

The first cycle contains all initial allocation and one full checked round.
Every further requested round is separately complete and physically admitted.
One classical result pack ends the original run. Structural reassociation only
changes sequence parentheses, retaining its complete states, paths, events,
chronological depth and both storage peaks. The zero-round endpoint is a
separate initialization-and-packing computation, not a restartable prefix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original caller requests one first complete cycle, the further rounds and the final pack. -/
public def positivePlan (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  .seq (.cycle (firstRoundProblem I A expansion nontrivial duration unitQueries))
    (completionPlan I A expansion nontrivial further duration unitQueries)

private def positiveAssociation (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat) :
    Circuit.Reassociation (code I A expansion nontrivial (further + 1))
      ((firstRound I A expansion nontrivial).seq
        ((reusedRounds I A expansion nontrivial further).seq (finalPack I A))) := by
  let initial := Sampling.Reuse.initialCode I A
  let retain := retainPersistent (model := Sampling.executionModel I A)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
  let body := round I A expansion nontrivial
  let rest := reusedRounds I A expansion nontrivial further
  let pack := finalPack I A
  exact (Circuit.Reassociation.seq (.refl initial) (.seqAssoc retain (body.seq rest) pack)).trans
    ((Circuit.Reassociation.seq (.refl initial)
      (.seq (.refl retain) (.seqAssoc body rest pack))).trans
      ((Circuit.Reassociation.seqAssoc initial retain (body.seq (rest.seq pack))).symm.trans
        (Circuit.Reassociation.seqAssoc (initial.seq retain) body (rest.seq pack)).symm))

private def groupedPositiveSchedule (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (positivePlan I A expansion nontrivial further duration unitQueries)
      ((firstRound I A expansion nontrivial).seq
        ((reusedRounds I A expansion nontrivial further).seq (finalPack I A))) :=
  .seq _ _
    (.complete _ (firstRoundCompleteCycle I A expansion nontrivial duration unitQueries))
    (completionSchedule I A expansion nontrivial further duration unitQueries)
    (by
      intro Reference original admitted
      cases further with
      | zero => exact ⟨True.intro, True.intro⟩
      | succ further =>
          exact ⟨True.intro, ecdlpRecovery_firstRound_nextInput_admitted I A expansion nontrivial
            original admitted.1⟩)
    (Or.inr ⟨ecdlpRecovery_firstRound_restartCleanup I A expansion nontrivial⟩)

/-- The actual original run, without replacing code, implements all requested complete cycles. -/
public def positiveSchedule (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (positivePlan I A expansion nontrivial further duration unitQueries)
      (code I A expansion nontrivial (further + 1)) :=
  .reassociate (positiveAssociation I A expansion nontrivial further)
    (groupedPositiveSchedule I A expansion nontrivial further duration unitQueries)

/-- Maximum cycle depth includes preparation and one whole round, never a raw inner iteration. -/
public theorem ecdlpRecovery_positive_maximumCycleDepth_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : (code I A expansion nontrivial (further + 1)).Path) :
    (positiveSchedule I A expansion nontrivial further duration unitQueries).maximumCycleDepth
      duration path ≤
        ResourcePool.weightedCount duration (firstRoundEventBudget I A expansion nontrivial) := by
  apply Circuit.CycleSchedule.maximumCycleDepth_reassociate_le
  intro groupedPath
  change max ((firstRound I A expansion nontrivial).depth duration groupedPath.1) _ ≤ _
  apply max_le
  · exact Circuit.depth_le_weightedCount_of_pool_le (firstRound I A expansion nontrivial) duration
      (firstRoundEventBudget I A expansion nontrivial) groupedPath.1
      (ecdlpRecovery_firstRound_events_le I A expansion nontrivial groupedPath.1)
  · refine (ecdlpRecovery_completion_maximumCycleDepth_le I A expansion nontrivial further
      duration unitQueries groupedPath.2).trans ?_
    rw [firstRoundEventBudget, ResourcePool.weightedCount_add]
    exact Nat.le_add_left _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
