/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-!
# Original checked-recovery numerical charge beside actual samples

Each actual sampled trace is counted before its original complete classical
attempt. The original numerical recovery ceiling includes decoding, checked
inversion, group-power verification and first-accepted selection. The final
option pack is counted once. No cardinality of a merged sampling branch pool
is substituted for the actual sample-event bound.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}
  (sampleCode : Circuit model ctx ctx false)
  (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
  (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
  (base target : CInputRef ctx (PointShape width))
  (sampleCount : Nat) (sampleBound : ∀ path, (sampleCode.eventTrace path).length ≤ sampleCount)

include sampleBound

/-- Every sample is followed by the original complete numerical classical-attempt ceiling. -/
lemma sampledAttempt_eventCount_original_le
    (path : (sampledAttempt sampleCode curve modulus sample base target).Path) :
    ((sampledAttempt sampleCode curve modulus sample base target).eventTrace
      path).length ≤
      sampleCount + (42 * scalarWidth + scalarWidth * (248 * width + 644) + 119) := by
  rw [sampledAttempt_eventTrace, List.length_append]
  exact Nat.add_le_add (sampleBound _)
    (attemptInto_eventCount_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2)

/-- Every declared round runs both its actual sampler and original complete checking. -/
lemma sampledAttempts_eventCount_original_le (count : Nat)
    (path : (sampledAttempts sampleCode count curve modulus sample base target).Path) :
    ((sampledAttempts sampleCode count curve modulus sample base target).eventTrace
      path).length ≤
        count * (sampleCount + (42 * scalarWidth + scalarWidth * (248 * width + 644) + 119)) :=
  Circuit.forRange_eventCount_le count
    (fun _ => sampledAttempt sampleCode curve modulus sample base target) _
    (fun _ iteration => sampledAttempt_eventCount_original_le sampleCode curve modulus
      sample base target sampleCount sampleBound iteration) path

/-- Seven initial retains add no event; all rounds and the final pack retain their actual charge. -/
lemma sampledRecoveryTail_eventCount_original_le (count : Nat)
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    ((sampledRecoveryTail sampleCode count curve modulus sample base target).eventTrace
      path).length ≤
        count * (sampleCount +
          (42 * scalarWidth + scalarWidth * (248 * width + 644) + 119)) + 1 := by
  rw [sampledRecoveryTail_eventTrace, List.length_append, List.length_singleton]
  exact Nat.add_le_add_right
    (sampledAttempts_eventCount_original_le sampleCode curve modulus sample base target
      sampleCount sampleBound count path.1.2) 1

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
