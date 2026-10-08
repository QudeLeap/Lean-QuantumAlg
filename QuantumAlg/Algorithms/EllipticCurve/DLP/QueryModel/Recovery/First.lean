/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Sequence
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Composition

/-!
# The actual first complete declared-query ECDLP cycle

One bank preparation and seven real retained cells precede the first complete
sampling/checking/feedback round. The first cycle ends only after that round's
actual measurements and physical reset. Preparation by itself is not a cycle
cut. No final option pack is inserted before a later quantum round.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private theorem initializedRound_events {model : ExecutionModel}
    {origin ctx : RuntimeCtx model.kind} (setup : Circuit model origin ctx)
    (width scalar : Nat)
    (body : Circuit model (persistentCtx ctx width scalar) (persistentCtx ctx width scalar))
    (setupBudget bodyBudget : ResourcePool model)
    (setupBound : ∀ path : setup.Path, setup.resourcePool path ≤ setupBudget)
    (bodyBound : ∀ path : body.Path, body.resourcePool path ≤ bodyBudget)
    (path : ((setup.seq (retainPersistent ctx width scalar)).seq body).Path) :
    ((setup.seq (retainPersistent ctx width scalar)).seq body).resourcePool path ≤
      setupBudget + bodyBudget := by
  change setup.resourcePool path.1.1 +
    (retainPersistent (model := model) ctx width scalar).resourcePool path.1.2 +
      body.resourcePool path.2 ≤ _
  rw [retainPersistent_resourcePool, add_zero]
  exact add_le_add (setupBound path.1.1) (bodyBound path.2)

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original one-time bank and persistent-latch allocations, with no sampling yet. -/
public def allocationCode (I : ECDLPInstance E) (A : Access I) :
    Circuit (Sampling.executionModel I A) (Sampling.pre I) (context I) :=
  (Sampling.Reuse.initialCode I A).seq
    (retainPersistent (model := Sampling.executionModel I A)
      (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I))

/-- The first actual complete computation includes allocation and all checked feedback. -/
public def firstRound (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit (Sampling.executionModel I A) (Sampling.pre I) (context I) :=
  (allocationCode I A).seq (round I A expansion nontrivial)

/-- Preparation is paid once in addition to the complete native round allowance. -/
public def firstRoundEventBudget (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) : ResourcePool (Sampling.executionModel I A) :=
  initializationBudget I A + roundEventBudget I A expansion nontrivial

/-- Full borrowed observations survive the same actual allocation prefix. -/
theorem ecdlpRecovery_allocation_restores (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Sampling.pre I) Reference
      ((Sampling.executionModel I A).HiddenState × History)) :
    (allocationCode I A).BorrowedRestored Reference state
      ((allocationCode I A).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (allocationCode I A) (by rfl) Reference state

/-- Every complete first-cycle record has the predetermined physical zero seed. -/
public theorem ecdlpRecovery_firstRound_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.ReinitializedAt (firstRound I A expansion nontrivial) (roundZeroSeed I) :=
  Circuit.RestartCleanup.afterAt (allocationCode I A) (round I A expansion nontrivial)
    (roundZeroSeed I) (ecdlpRecovery_round_reinitializedAt I A expansion nontrivial)

/-- A further quantum round starts only after the actual first complete physical cleanup. -/
public theorem ecdlpRecovery_firstRound_restartCleanup (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.RestartCleanup (firstRound I A expansion nontrivial) :=
  Circuit.RestartCleanup.after (allocationCode I A) (round I A expansion nontrivial)
    (by
      intro Reference History _ state
      exact ecdlpRecovery_allocation_restores I A state)
    (ecdlpRecovery_round_restartCleanup I A expansion nontrivial)

/-- The actual first cycle charges preparation and every sampling/recovery event. -/
public theorem ecdlpRecovery_firstRound_events_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (path : (firstRound I A expansion nontrivial).Path) :
    (firstRound I A expansion nontrivial).resourcePool path ≤
      firstRoundEventBudget I A expansion nontrivial := by
  exact initializedRound_events (Sampling.Reuse.initialCode I A) (fieldWidth E) (scalarWidth I)
    (round I A expansion nontrivial) (initializationBudget I A)
    (roundEventBudget I A expansion nontrivial)
    (fun path => (initialization_events I A path).le)
    (ecdlpRecovery_round_events_le I A expansion nontrivial) path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
