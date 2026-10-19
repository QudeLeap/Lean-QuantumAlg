/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Restart
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Sampling.Reuse.Restart
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Restart
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources

/-!
# The complete actual declared-query ECDLP sampling and recovery round

Each chronological loop body includes both physical resets, the sole original
declared group query, real exponent readout, full checked raw recovery, curve
verification and first-success feedback. The seven actual recovery cells stay
live throughout. Physical restart is proved after all that feedback, separately
from the independent protocol and actual next-input admission obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private def seedUnderPersistent {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (width scalar : Nat) (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ) :
    (persistentCtx ctx width scalar).quantumLayout.SelectedBasis
      (persistentCtx ctx width scalar).borrowedSelectionᶜ := seed

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The unchanged full bank and original public points coexist with all seven recovery cells. -/
public def context (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)

/-- One original chronological body, including complete paid recovery and first-success feedback. -/
public def round (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit (Sampling.executionModel I) (context I) (context I) :=
  sampledAttempt (Sampling.Reuse.code (allowAllocation := false) I expansion)
    (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)

/-- The chronological body reserves both resets and every original checked native operation. -/
public def roundEventBudget (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) : ResourcePool (Sampling.executionModel I) :=
  Sampling.Reuse.eventBudget I expansion +
    attemptEnvelope (Sampling.executionModel I) (curve E) (modulus I nontrivial)

/-- The fixed physical zero seed does not depend on the recovered candidate or actual record. -/
public def roundZeroSeed (I : ECDLPInstance E) :
    (context I).quantumLayout.SelectedBasis (context I).borrowedSelectionᶜ :=
  seedUnderPersistent (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
    (Sampling.Reuse.zeroSeed I)

/-- Complete real recovery and feedback preserve the same fixed owned physical seed. -/
public lemma ecdlpRecovery_round_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.ReinitializedAt (round I expansion nontrivial) (Sampling.sourceEnvironment I A)
      (roundZeroSeed I) :=
  sampledAttempt_reinitializedAt (Sampling.Reuse.code (allowAllocation := false) I expansion)
    (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) (Sampling.Reuse.zeroSeed I)
    (Sampling.Reuse.ecdlpReuse_code_reinitializedAt (allowAllocation := false) I A expansion)
    (Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I)

/-- The complete real sampling/checking/feedback section is physically restartable. -/
public lemma ecdlpRecovery_round_restartCleanup (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.RestartCleanup (round I expansion nontrivial) (Sampling.sourceEnvironment I A) :=
  sampledAttempt_restartCleanup (Sampling.Reuse.code (allowAllocation := false) I expansion)
    (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    (Sampling.Reuse.ecdlpReuse_code_restartCleanup (allowAllocation := false) I A expansion)
    (Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I)

/-- The physical certificate belongs to the same chronological body used by the real finite run. -/
lemma ecdlpRecovery_round_is_loopBody (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    sampledAttempts (Sampling.Reuse.code (allowAllocation := false) I expansion)
      count (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) =
        Circuit.forRange count (fun _ => round I expansion nontrivial) := rfl

/-- Every actual body path pays the entire sample and checked-recovery event allowance. -/
public lemma ecdlpRecovery_round_events_le (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (path : (round I expansion nontrivial).Path) :
    (round I expansion nontrivial).resourcePool path ≤
      roundEventBudget I expansion nontrivial :=
  sampledAttempt_pool_le (Sampling.Reuse.code (allowAllocation := false) I expansion)
    (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    (Sampling.Reuse.eventBudget I expansion)
    (Sampling.Reuse.ecdlpReuse_code_events_le (allowAllocation := false) I expansion) path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
