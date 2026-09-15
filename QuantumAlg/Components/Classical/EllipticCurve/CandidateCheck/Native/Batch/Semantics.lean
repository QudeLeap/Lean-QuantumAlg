/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Semantics

/-!
# Actual chronological recovery-attempt loop

Once the seven persistent cells exist, every indexed sample runs the same
original six-stage attempt on its predecessor's returned store. The complete
record preserves all quantum-reference blocks and original history and records
every actual path. Its final store is exactly the chronological fold of those
actual updates, including the identity loop at zero attempts.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth count : Nat}

/-- The original actual six-stage store update uses the same seven allocated destinations. -/
def persistentAttemptStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    Store (persistentCtx ctx width scalarWidth) → Store (persistentCtx ctx width scalarWidth) :=
  attemptStore curve modulus (persistentInput width scalarWidth sample)
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth)

/-- Actual sample updates are folded in the original increasing finite-index order. -/
def repeatedAttemptsStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth)) :
    Store (persistentCtx ctx width scalarWidth) :=
  (List.ofFn (fun index => persistentAttemptStore curve modulus (samples index) base target)).foldl
    (fun current update => update current) before

/-- Every loop iteration uses the real previous store and preserves the complete reference. -/
theorem repeatedAttempts_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    ∃ record : Store (persistentCtx ctx width scalarWidth) →
        Store (persistentCtx ctx width scalarWidth) ×
          (repeatedAttempts curve modulus samples base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State (persistentCtx ctx width scalarWidth) Reference History),
        (repeatedAttempts curve modulus samples base target).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store (persistentCtx ctx width scalarWidth), (record before).1 =
        repeatedAttemptsStore curve modulus samples base target before := by
  have each := fun index : Fin count => attemptInto_actualRecord curve modulus
    (persistentInput width scalarWidth (samples index))
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth)
  choose records equations stores using each
  refine ⟨Circuit.forRangeRecord count _ records,
    Circuit.execute_forRangeRecord count _ records equations, ?_⟩
  intro before
  refine (Circuit.forRangeRecord_store count
    (fun index => persistentAttempt curve modulus (samples index) base target)
    records before).trans ?_
  have updates : List.ofFn (fun index => fun current => (records index current).1) =
      List.ofFn (fun index => persistentAttemptStore curve modulus (samples index) base target) :=
    congrArg List.ofFn (funext fun index => funext fun current => stores index current)
  rw [updates]
  rfl

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
