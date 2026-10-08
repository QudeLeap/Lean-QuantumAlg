/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing.Solves
import all QuantumAlg.Core.Execution.CycleSchedule.Bounds

/-!
# One actual final option pack after the finite complete-round suffix

The existing first-success bit and selected word are encoded once, after all
requested rounds, by the original paid classical instruction. Its independent
deterministic contract restores borrowed observations and accounts for the
new real option cell. The chronological circuit still pays this terminal work;
it is not another quantum cycle and introduces no reset or quantum bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original single retained optional-result cell and native option-pack instruction. -/
public def finalPack (I : ECDLPInstance E) (A : Access I) :
    Circuit (Sampling.executionModel I A) (context I) (post I) :=
  packBatchResult (model := Sampling.executionModel I A)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- Independent certain encoding of the actual incoming first-success result cells.

**Input.** Any existing persistent store, joint service state and external reference.
**Output.** The original accepted bit and selected word encoded as one optional result,
with every prior live entry and borrowed observation retained.
**Resource budget.** One actual width-indexed native option-pack operation and
one new retained optional word beside both complete existing storage pools.
**Success.** Exact encoding of the actual incoming latches with probability one.
**Source.** The library's closed `CShape.packOption` semantics and original checked
batch's actual terminal instruction; no additional quantum computation is claimed.
-/
public def finalPackProblem (I : ECDLPInstance E) (A : Access I) :
    Problem (Sampling.executionModel I A) (context I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  BatchPacking.problem (model := Sampling.executionModel I A)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- The paid actual result pack has a complete independently certified classical protocol. -/
public def finalPackSchedule (I : ECDLPInstance E) (A : Access I) :
    Circuit.CycleSchedule (.classical (finalPackProblem I A)) (finalPack I A) :=
  BatchPacking.schedule (model := Sampling.executionModel I A)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- Exactly the requested reused complete rounds, followed by one classical optional pack. -/
public def completionPlan (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (Sampling.executionModel I A) (context I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  .seq (reusedRoundPlan I A expansion nontrivial count duration unitQueries)
    (.classical (finalPackProblem I A))

/-- The same actual range and the sole final pack implement the requested completed suffix. -/
public def completionSchedule (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (completionPlan I A expansion nontrivial count duration unitQueries)
      ((reusedRounds I A expansion nontrivial count).seq (finalPack I A)) :=
  .seq _ _ (reusedRoundSchedule I A expansion nontrivial count duration unitQueries)
    (finalPackSchedule I A) (by intro _ _ _; exact ⟨True.intro, True.intro⟩)
    (Or.inl (BatchPacking.onlyClassical (model := Sampling.executionModel I A)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))

/-- Terminal classical work adds no quantum cycle while retaining the complete round allowance. -/
public theorem ecdlpRecovery_completion_maximumCycleDepth_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1)
    (path : ((reusedRounds I A expansion nontrivial count).seq (finalPack I A)).Path) :
    (completionSchedule I A expansion nontrivial count duration unitQueries).maximumCycleDepth
      duration path ≤
        ResourcePool.weightedCount duration (roundEventBudget I A expansion nontrivial) := by
  change max (_ : Nat) 0 ≤ _
  rw [max_eq_left (Nat.zero_le _)]
  exact ecdlpRecovery_reused_maximumCycleDepth_le I A expansion nontrivial count
    duration unitQueries path.1

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
