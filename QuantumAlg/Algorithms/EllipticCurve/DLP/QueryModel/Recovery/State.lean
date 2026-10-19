/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation.State
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing.State
import all QuantumAlg.Core.Execution.Restart.Range
import all QuantumAlg.Core.Execution.Restart.Reassociation
import all QuantumAlg.Core.Execution.Classical.Composition

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion

/-!
# Every original finite run has the same complete owned zero output
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

attribute [local irreducible] persistentCtx

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The prescribed full output zero state includes the actual final retained option cell. -/
public def wholeZeroSeed (I : ECDLPInstance E) :
    (post I).quantumLayout.SelectedBasis (post I).borrowedSelectionᶜ :=
  finalPackSeed (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I) (roundZeroSeed I)

/-- The original caller's positive full run has the same physical zero seed after its sole pack. -/
public lemma ecdlpRecovery_positiveCode_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (further : Nat) :
    Circuit.ReinitializedAt (code I expansion nontrivial (further + 1))
      (Sampling.sourceEnvironment I A) (wholeZeroSeed I) := by
  let retain := retainPersistent (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
  let rounds := reusedRounds I expansion nontrivial (further + 1)
  let packing := finalPack I
  have roundsFixed := Circuit.RestartCleanup.constantRange_reinitializedAt (environment :=
    Sampling.sourceEnvironment I A)
    (round I expansion nontrivial) (roundZeroSeed I)
    (ecdlpRecovery_round_reinitializedAt I A expansion nontrivial) further
  have retainedFixed := Circuit.RestartCleanup.afterAt (environment := Sampling.sourceEnvironment
    I A) retain rounds (roundZeroSeed I) roundsFixed
  have packedFixed := packedReinitializedAt (environment := Sampling.sourceEnvironment I A)
    (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E)
    (scalarWidth I) (retain.seq rounds) (roundZeroSeed I) retainedFixed
  exact Circuit.RestartCleanup.afterAt (environment := Sampling.sourceEnvironment I A)
    (Sampling.Reuse.initialCode I)
    ((retain.seq rounds).seq packing) (wholeZeroSeed I) packedFixed



private def zeroCodeAssociation (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.Reassociation (code I expansion nontrivial 0)
      (((allocationCode I).seq
        (Circuit.id (model := Sampling.executionModel I) (context I))).seq (finalPack I)) := by
  let initial := Sampling.Reuse.initialCode I
  let retain := retainPersistent (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
  let empty := Circuit.id (allowAllocation := true)
    (model := Sampling.executionModel I) (context I)
  let pack := finalPack I
  exact (Circuit.Reassociation.seq (.refl initial) (.seqAssoc retain empty pack)).trans
    ((Circuit.Reassociation.seqAssoc initial retain (empty.seq pack)).symm.trans
      (Circuit.Reassociation.seqAssoc (initial.seq retain) empty pack).symm)

/-- The original zero-round computation still allocates and packs, preserving the full zero bank. -/
public lemma ecdlpRecovery_zeroCode_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.ReinitializedAt (code I expansion nontrivial 0) (Sampling.sourceEnvironment I A)
      (wholeZeroSeed I) := by
  let empty := Circuit.id (allowAllocation := true)
    (model := Sampling.executionModel I) (context I)
  have fixed := Circuit.RestartCleanup.followedByMapAt (environment := Sampling.sourceEnvironment
    I A) (allocationCode I) empty
    (roundZeroSeed I) (ecdlpRecovery_allocation_reinitializedAt I A) (fun entry => (entry, ()))
    (by
          intro Reference History _ state
          have identity := Circuit.execute_id_mapClassical (environment :=
            Sampling.sourceEnvironment I A) (allowAllocation := true)
            (model := Sampling.executionModel I) (ctx := context I) Reference state
          refine identity.trans ?_
          exact ExecutionState.executionState_mapClassical_congr_decision state _ _
            (by intro entry; rfl) _ _)
  have packed := packedReinitializedAt (environment := Sampling.sourceEnvironment I A)
    (model := Sampling.executionModel I)
    (Sampling.Reuse.context I) (fieldWidth E)
    (scalarWidth I) ((allocationCode I).seq empty) (roundZeroSeed I) fixed
  exact Circuit.RestartCleanup.reassociatedAt (environment := Sampling.sourceEnvironment I A)
    (zeroCodeAssociation I expansion nontrivial)
    (wholeZeroSeed I) packed

/-- Every prescribed finite count, including zero, has the actual fixed full owned output seed. -/
public lemma ecdlpRecovery_code_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Circuit.ReinitializedAt (code I expansion nontrivial count) (Sampling.sourceEnvironment I A)
      (wholeZeroSeed I) := by
  cases count with
  | zero => exact ecdlpRecovery_zeroCode_reinitializedAt I A expansion nontrivial
  | succ further =>
      exact ecdlpRecovery_positiveCode_reinitializedAt I A expansion nontrivial further

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
