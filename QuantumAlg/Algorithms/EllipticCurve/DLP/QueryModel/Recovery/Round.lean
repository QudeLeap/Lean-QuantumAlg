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
public def round (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit (Sampling.executionModel I A) (context I) (context I) :=
  sampledAttempt (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)

/-- The chronological body reserves both resets and every original checked native operation. -/
public def roundEventBudget (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) : ResourcePool (Sampling.executionModel I A) :=
  Sampling.Reuse.eventBudget I A expansion +
    attemptEnvelope (Sampling.executionModel I A) (curve E) (modulus I nontrivial)

/-- The fixed physical zero seed does not depend on the recovered candidate or actual record. -/
public def roundZeroSeed (I : ECDLPInstance E) :
    (context I).quantumLayout.SelectedBasis (context I).borrowedSelectionᶜ :=
  seedUnderPersistent (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)
    (Sampling.Reuse.zeroSeed I)

/-- Complete real recovery and feedback preserve the same fixed owned physical seed. -/
public theorem ecdlpRecovery_round_reinitializedAt (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.ReinitializedAt (round I A expansion nontrivial) (roundZeroSeed I) :=
  sampledAttempt_reinitializedAt (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) (Sampling.Reuse.zeroSeed I)
    (Sampling.Reuse.ecdlpReuse_code_reinitializedAt I A expansion)
    (Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I)

/-- The complete real sampling/checking/feedback section is physically restartable. -/
public theorem ecdlpRecovery_round_restartCleanup (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) :
    Circuit.RestartCleanup (round I A expansion nontrivial) :=
  sampledAttempt_restartCleanup (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    (Sampling.Reuse.ecdlpReuse_code_restartCleanup I A expansion)
    (Sampling.Reuse.ecdlpReuse_noBorrowedQuantum I)

/-- The physical certificate belongs to the same chronological body used by the real finite run. -/
theorem ecdlpRecovery_round_is_loopBody (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    sampledAttempts (Sampling.Reuse.code I A expansion)
      (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) count (curve E) (modulus I nontrivial)
      (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I) =
        Circuit.forRange count (fun _ => round I A expansion nontrivial) := rfl

/-- Every actual body path pays the entire sample and checked-recovery event allowance. -/
public theorem ecdlpRecovery_round_events_le (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (path : (round I A expansion nontrivial).Path) :
    (round I A expansion nontrivial).resourcePool path ≤
      roundEventBudget I A expansion nontrivial :=
  sampledAttempt_pool_le (Sampling.Reuse.code I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_isLocal I A expansion) (curve E) (modulus I nontrivial)
    (Sampling.Reuse.sampleInput I) (baseInput I) (targetInput I)
    (Sampling.Reuse.eventBudget I A expansion)
    (Sampling.Reuse.ecdlpReuse_code_events_le I A expansion) path

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
