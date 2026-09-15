/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Cardinality
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Exposure.Cardinality

/-!
# Original numerical ceiling for one actual verified recovery attempt

The actual three-cell recovery, group-power target verification and original
first-accepted selector are all charged. The seven persistent destinations
are allocated outside this attempt; no event or space allocation is invented
to replace the real sequential execution.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open FiniteCyclicDLP.RawRecovery.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The actual complete attempt retains the original public numerical event ceiling. -/
theorem attemptEnvelope_card_le (kind : ProblemKind) (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth) :
    (attemptEnvelope kind curve modulus).card ≤
      42 * scalarWidth + scalarWidth * (248 * width + 644) + 119 := by
  have recovery := singleExposureEnvelope_card_le kind modulus
  have verification := verificationEnvelope_card_le kind curve scalarWidth
  rw [attemptEnvelope, Multiset.card_add, Multiset.card_add,
    FirstAccepted.firstAccepted_nativeEnvelope_card]
  omega

/-- Every actual path of the original six-stage attempt satisfies its original event bound. -/
theorem attemptInto_eventCount_le (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess : CWriteRef ctx .bit) (candidate : CWriteRef ctx (.unsignedWord scalarWidth))
    (reconstruction : CWriteRef ctx .bit) (scalarResult : CWriteRef ctx (PointShape width))
    (targetAccepted accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord scalarWidth))
    (path : (attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).Path) :
    ((attemptInto curve modulus sample base target inverseSuccess candidate reconstruction
      scalarResult targetAccepted accepted selected).eventTrace path).length ≤
        42 * scalarWidth + scalarWidth * (248 * width + 644) + 119 :=
  (Multiset.card_le_card (attemptInto_pool_le curve modulus sample base target inverseSuccess
    candidate reconstruction scalarResult targetAccepted accepted selected path)).trans
      (attemptEnvelope_card_le kind curve modulus)

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
