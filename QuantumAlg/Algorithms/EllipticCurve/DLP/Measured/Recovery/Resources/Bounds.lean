/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Time
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Time

/-!
# Quantum time and space of the same finite streaming run

The exact actual finite-loop component paths are bounded individually and
summed. Allocation, each real reset, every converted sampler, the complete
native checker and the final paid option packing remain in the original run.
The resulting time and qubit bounds concern the same run and the same Path.

These bounds concern quantum time and space; endpoint success and Algorithm.Solves have
separate owners.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Bounds

noncomputable section

open QuantumAlg.Execution
open FiniteCyclicDLP (KnownOrderProblem orderWidth)
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
  (sampledAttempt)
open scoped BigOperators

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ) (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Every actual attempt, including reset, contributes the same independent scalar ceiling. -/
lemma run_quantumTime_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.quantumTime path ≤
      count * ((Recovery.Layout.terminal p.size (orderWidth problem)).systemCount +
        (4 * MAU.Multiplication.Gidney.eventBound p.size +
          2 * orderWidth problem *
            (MeasuredPointAddition.depthBound p.size + 2 * orderWidth problem + 13))) := by
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
  let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
  let attempt := sampledAttempt sampleCode curve modulus sample base target
  let placed := Circuit.embed (allowAllocation := false)
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed r points coefficient)
  let original (index : Fin count) :=
    (BitWord.selectForCircuitPathEquiv placed).symm
      (Time.sampledAttemptSamplePath sampleCode curve modulus sample base target
        (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index))
  rw [Time.streamingRecovery_run_quantumTime]
  change (∑ index : Fin count,
    ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).quantumTime
        (original index).1 +
      (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
        coefficient).quantumTime (original index).2)) ≤ _
  refine (Finset.sum_le_sum (g := fun _ : Fin count =>
    (Recovery.Layout.terminal p.size (orderWidth problem)).systemCount +
      (4 * MAU.Multiplication.Gidney.eventBound p.size +
        2 * orderWidth problem *
          (MeasuredPointAddition.depthBound p.size + 2 * orderWidth problem + 13))) ?_).trans_eq ?_
  · intro index _
    have reset := Recovery.Initialization.Time.newReset_quantumTime_le E fieldTail
      (orderWidth problem) seed (original index).1
    have converted := Recovery.Conversion.Time.convertedStages_quantumTime_le E r points
      (Recovery.Layout.order (orderWidth problem)) coefficient (original index).2
    have bounded := Nat.add_le_add reset converted
    simpa only [Recovery.Layout.order, List.length_finRange] using bounded
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]


end

end ExecutionContract.Bounds
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
