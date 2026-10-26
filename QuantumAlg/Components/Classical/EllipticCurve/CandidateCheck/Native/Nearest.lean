/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling

/-!
# Actual repeated sampling with nearest recovery and candidate checking

Each round executes the supplied sampler, the paid nearest raw decoder, the
original checked inverse and scalar candidate verification, and the actual
first-success latch.  Seven persistent destinations are allocated once and
reused; one final optional result is packed after the complete fixed-count loop.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width scalarWidth : Nat}

/-- One actual nearest-recovered sample is checked and entered in the original
first-success latch using the existing seven persistent cells. -/
def persistentAttempt (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  attemptInto curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth)

/-- Every round runs a fresh actual sample and immediately applies nearest
recovery, candidate verification and the shared persistent first-success latch. -/
def sampledAttempt (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  (sampleUnderPersistent sampleCode width scalarWidth).seq
    (persistentAttempt curve modulus sample base target)

/-- The same literal nearest-recovery attempt executes exactly the public round count. -/
def sampledAttempts (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  Circuit.forRange count fun _ => sampledAttempt sampleCode curve modulus sample base target

/-- Actual persistent-cell retention and final option packing enclose all attempts. -/
def sampledRecoveryTail (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Circuit model ctx (batchResultCtx ctx width scalarWidth) :=
  ((retainPersistent ctx width scalarWidth).seq
    (sampledAttempts sampleCode count curve modulus sample base target)).seq
      (packBatchResult ctx width scalarWidth)

/-- The complete actual nearest-recovery run reads its final stored option and
lists every final live entry exactly once. -/
def sampledRecoveryRun (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    AlgorithmRun model ctx (batchResultCtx ctx width scalarWidth)
      (.option (.unsignedWord scalarWidth)) where
  code := sampledRecoveryTail sampleCode count curve modulus sample base target
  output := Output.all (batchResultCtx ctx width scalarWidth)
    (.read (batchResultRead ctx width scalarWidth))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
