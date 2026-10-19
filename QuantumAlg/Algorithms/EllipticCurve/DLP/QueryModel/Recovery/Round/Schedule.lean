/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Solves
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Admission
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round
import all QuantumAlg.Core.Algorithm.Identity
import all QuantumAlg.Core.Execution.Restart.Admission
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Actual finite schedule of complete reused ECDLP rounds

Every requested round is an independently specified complete computation with
original success, native checked feedback, physical reset and real next-input
admission. The actual zero-length range tail is classical identity work.
Maximum complete-cycle depth bounds one whole sampling/checking/reset round;
the actual sequential depth and total events retain all requested rounds.
Initial allocation and the one final optional pack remain separate endpoint
obligations; this reused suffix does not certify the original whole run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The named actual finite loop uses the original complete round at every prescribed index. -/
public def reusedRounds (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat) :
    Circuit (Sampling.executionModel I) (context I) (context I) :=
  Circuit.forRange count (fun _ => round I expansion nontrivial)

/-- Actual history projection preserves the predetermined seed after complete feedback. -/
public lemma ecdlpRecovery_round_nextInput_seeded (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) {Reference : Register}
    (original : OracleInput (Sampling.executionModel I).classicalOracles (context I) Reference) :
    roundSeededDomain I ((round I expansion nontrivial).nextInput (Sampling.sourceEnvironment I A)
      original).localState :=
  Circuit.ReinitializedAt.nextInput_jointSeeded (environment := Sampling.sourceEnvironment I A)
    (round I expansion nontrivial) (roundZeroSeed I)
    (ecdlpRecovery_round_reinitializedAt I A expansion nontrivial) original

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
