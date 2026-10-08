/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.NativePool
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Core.Execution.Circuit.Weighted

/-!
# Complete native event pool of the actual repeated ECDLP run

The original one-time initialization is embedded into the selected model.
Every actual reset, sampling, readout and checked-recovery event is charged
per round, followed by the final optional-result packing event even at zero
rounds.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- One original initialization, all actual rounds and the final pack instruction. -/
def repeatedRunBudget :
    ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model) :=
  BitWord.liftQuantumPool
      (ResourcePool.ofList (Allocation.initializationTrace p (2 * orderWidth problem))) +
    sampledRecoveryEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
      (BitWord.liftQuantumPool (samplingRoundBudget E problem))
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) count

omit [Fact p.Prime] in
/-- Exact size of the independent complete-run allowance: one initialization,
`count` complete sampling and recovery rounds, and one final option pack. -/
theorem repeatedRunBudget_card :
    (repeatedRunBudget E problem nontrivial count).card =
      (Allocation.initializationTrace p (2 * orderWidth problem)).length +
        count * ((samplingRoundBudget E problem).card +
          (attemptEnvelope (.quantum AlgorithmGate.model .empty BitWord.model)
            (Canonical.Layout.curveSpec E)
            (recoveryModulusSpec problem nontrivial)).card) + 1 := by
  simp [repeatedRunBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.scale, ResourcePool.ofList,
    Nat.mul_add, add_assoc]

/-- The complete actual repeated code is bounded by its native event allowance. -/
theorem exponentRepeatedCode_pool_le
    (path : (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Path) :
    (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).resourcePool path ≤
        repeatedRunBudget E problem nontrivial count := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (le_of_eq (selectedInitial_pool_eq E problem path.1))
    (sampledRecoveryTail_pool_le
      (BitWord.selectForCircuit
        (samplingRound E fieldTail sameWidth fits odd problem points seed))
      (BitWord.selectForCircuit_isLocal _
        (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed)) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _
      (BitWord.liftQuantumPool (samplingRoundBudget E problem))
      (selectedSamplingRound_pool_le E fieldTail sameWidth fits odd problem points seed) path.2)

/-- The same complete event allowance bounds the actual critical path at arbitrary native costs. -/
theorem exponentRepeatedCode_depth_le
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model) → Nat)
    (path : (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).Path) :
    (exponentRepeatedCode E fieldTail sameWidth fits odd problem points seed
      nontrivial count).depth duration path ≤
        ResourcePool.weightedCount duration (repeatedRunBudget E problem nontrivial count) :=
  Circuit.depth_le_weightedCount_of_pool_le _ duration _ path
    (exponentRepeatedCode_pool_le E fieldTail sameWidth fits odd problem points seed
      nontrivial count path)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
