/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained.Semantics
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Correctness

/-!
# Original acceptance of actual retained candidate verification

Real retention supplies every destination-separation condition internally.
The original candidate, represented base and represented target are the only
semantic inputs. The actual retained bit accepts exactly the original scalar
equation together with the original inverse and reconstruction success flags.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The retained actual acceptance is the original target equation and both actual success flags. -/
theorem retainedStep_accepts_iff {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (before : Store ctx) (hidden : model.HiddenState)
    (scalar : ClassicalAlgorithms.Word scalarWidth)
    (basePoint targetPoint : Pure.Point spec)
    (candidateValue : before.read candidate = .unsignedWord scalar)
    (baseRep : PointRepresents spec (before.read base) basePoint)
    (targetRep : PointRepresents spec (before.read target) targetPoint) :
    ((retainedStep spec candidate base target inverseSuccess reconstruction
      (before, hidden)).1.1.read
        (.storage (retainedAccepted ctx width).toCStorageRef)).toBool = true ↔
      scalar.val • basePoint = targetPoint ∧
        (before.read inverseSuccess).toBool = true ∧
        (before.read reconstruction).toBool = true := by
  have actual := verifyStep_accepts_iff spec (retainedInput width candidate)
    (retainedInput width base) (retainedInput width target) (retainedInput width inverseSuccess)
    (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width)
    (retainedInitialStore width before) hidden scalar basePoint targetPoint
    ((retainedInitialStore_read width before candidate).trans candidateValue)
    (by rw [retainedInitialStore_read]; exact baseRep)
    (by rw [retainedInitialStore_read]; exact targetRep)
    (retainedScalar_separate width candidate) (retainedScalar_separate width base)
    (retainedScalar_separate width target) (retainedScalar_separate width inverseSuccess)
    (retainedScalar_separate width reconstruction) (retainedAccepted_separate width inverseSuccess)
    (retainedAccepted_separate width reconstruction)
  rw [retainedInitialStore_read, retainedInitialStore_read] at actual
  exact actual

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
