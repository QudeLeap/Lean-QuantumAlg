/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.CycleSchedule.Cleanup.Deterministic
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Classical.Composition
public import QuantumAlg.Core.Algorithm.AlgorithmRun.FixedOutput

/-!
# Complete-round zero state after actual result observation

The real sampler, native check and first-success feedback leave the same
predetermined physical seed in every complete record. Summing unobserved
histories and conditioning on the existing two-cell result preserve this
mass-weighted pure promise, including zero-mass output fibers.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

attribute [local instance] Classical.decEq
attribute [local irreducible] ExecutionState.mapClassical


variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every actual observed complete-round result has the same fixed zero owned-bank state. -/
public theorem ecdlpRecovery_round_stateRequirement (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I A).classicalOracles (context I) Reference) :
    (roundStateRequirement I).Holds original.caller
      ((roundAlgorithm I A expansion nontrivial).run.finalState Reference original.state) :=
  AlgorithmRun.stateRequirement_of_reinitializedAt
    (roundAlgorithm I A expansion nontrivial).run (roundZeroSeed I)
    (ecdlpRecovery_round_reinitializedAt I A expansion nontrivial) (roundResultRead I) original

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
