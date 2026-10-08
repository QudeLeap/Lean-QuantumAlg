/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Solves
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Protocol

/-!
# The original zero and positive finite runs have complete actual schedules
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Every zero-count run is a complete terminal initialization-and-packing computation. -/
public def zeroCompleteCycle (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CompleteCycle (code I A expansion nontrivial 0)
      (wholeProblem I A expansion nontrivial 0 duration unitQueries) where
  output := (run I A expansion nontrivial 0).output
  certified := ecdlpRecovery_whole_solves I A expansion nontrivial 0 duration unitQueries

/-- Zero is the complete original terminal run; positive counts use actual first/reused cycles. -/
public def finitePlan (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CyclePlan (Sampling.executionModel I A) (Sampling.pre I) (post I)
      (.option (.unsignedWord (scalarWidth I))) :=
  match count with
  | 0 => .cycle (wholeProblem I A expansion nontrivial 0 duration unitQueries)
  | further + 1 => positivePlan I A expansion nontrivial further duration unitQueries

/-- The same actual finite code has its complete protocol and physical cycle schedule. -/
public def finiteSchedule (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order) (count : Nat)
    (duration : Resource.Event (Sampling.executionModel I A) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Circuit.CycleSchedule (finitePlan I A expansion nontrivial count duration unitQueries)
      (code I A expansion nontrivial count) := by
  cases count with
  | zero => exact .complete _ (zeroCompleteCycle I A expansion nontrivial duration unitQueries)
  | succ further => exact positiveSchedule I A expansion nontrivial further duration unitQueries

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
