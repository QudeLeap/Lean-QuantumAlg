/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Semantics

/-!
# Paid nearest recovery through actual candidate verification and first-success selection

The existing native verifier and selector consume the actual nearest decoder's
three exposed cells.  All chronological stores, path records, caller reads,
Reference matrices and prior History labels remain part of the same execution.
The generic truncated-range decoder and its existing consumers are unchanged.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- One actual six-stage record uses the same seven allocated destinations. -/
noncomputable def persistentAttemptRecord (curve : CurveSpec width)
    (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Store (persistentCtx ctx width scalarWidth) × model.HiddenState →
      (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
        (persistentAttempt curve modulus sample base target).Path :=
  Classical.choose (attemptInto_actualRecord (environment := environment) curve modulus
    (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth))

/-- The actual six-stage attempt updates the caller store and persistent service state. -/
def persistentAttemptState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) × model.HiddenState :=
  (persistentAttemptRecord (environment := environment) curve modulus sample base target before).1

/-- The caller store is the store projection of the actual six-stage state update. -/
def persistentAttemptStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) :=
  (persistentAttemptState (environment := environment) curve modulus sample base target before).1


end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
