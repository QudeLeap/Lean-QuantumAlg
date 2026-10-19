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

/-- Actual sample and service-state updates fold in increasing finite-index order. -/
def repeatedAttemptsState (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) × model.HiddenState :=
  (List.ofFn (fun index => persistentAttemptState (environment := environment) curve modulus
    (samples index) base target)).foldl
    (fun current update => update current) before

/-- The final caller store is the projection of that same actual chronological fold. -/
def repeatedAttemptsStore (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState) :
    Store (persistentCtx ctx width scalarWidth) :=
  (repeatedAttemptsState (environment := environment) curve modulus samples base target before).1

/-- Every loop iteration uses the real previous store and preserves the complete reference. -/
lemma repeatedAttempts_actualRecord (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) :
    ∃ record : Store (persistentCtx ctx width scalarWidth) × model.HiddenState →
        (Store (persistentCtx ctx width scalarWidth) × model.HiddenState) ×
          (repeatedAttempts curve modulus samples base target).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State (persistentCtx ctx width scalarWidth) Reference
          (model.HiddenState × History)),
        (repeatedAttempts curve modulus samples base target).execute environment Reference state =
          state.mapClassical (fun entry =>
            let result := record (entry.1, entry.2.1)
            (result.1.1, (result.1.2, (entry.2.2, result.2))))) ∧
      ∀ before : Store (persistentCtx ctx width scalarWidth) × model.HiddenState,
        (record before).1.1 =
        repeatedAttemptsStore (environment := environment) curve modulus samples base target
          before := by
  have each := fun index : Fin count => attemptInto_actualRecord (environment := environment)
    curve modulus
    (persistentInput width scalarWidth (samples index))
    (persistentInput width scalarWidth base) (persistentInput width scalarWidth target)
    (persistentInverseSuccess ctx width scalarWidth) (persistentCandidate ctx width scalarWidth)
    (persistentReconstruction ctx width scalarWidth) (persistentScalar ctx width scalarWidth)
    (persistentTargetAccepted ctx width scalarWidth) (persistentAccepted ctx width scalarWidth)
    (persistentSelected ctx width scalarWidth)
  let records := fun index : Fin count =>
    persistentAttemptRecord (environment := environment) curve modulus (samples index) base target
  have equations : ∀ index (Reference : Register) {History : Type} [Fintype History]
      (state : State (persistentCtx ctx width scalarWidth) Reference
        (model.HiddenState × History)),
      (persistentAttempt curve modulus (samples index) base target).execute environment
        Reference state =
        state.mapClassical (fun entry =>
          let result := records index (entry.1, entry.2.1)
          (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
    intro index Reference History _ state
    exact (Classical.choose_spec (each index)).1 Reference state
  refine ⟨Circuit.forRangeRecord count _ records,
    Circuit.execute_forRangeRecord (environment := environment) count _ records equations, ?_⟩
  intro before
  exact Circuit.forRangeRecord_store count
    (fun index => persistentAttempt curve modulus (samples index) base target) records before

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
