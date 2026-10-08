/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Invariant
import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Correctness

/-!
# Actual finite refinement reaches the original final interval
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {inputWidth : Nat}

/-- Every actual round preserves caller reads outside the original round write identities. -/
theorem roundsStep_callerFrame (refs : Refs ctx inputWidth) (remaining : Nat)
    (store : Store ctx) :
    IntegerSqrt.CallerFrame refs.round store (roundsStep (model := model) refs remaining store).1
      := by
  induction remaining generalizing store with
  | zero => intro shape other _avoids; rfl
  | succ remaining inductionHypothesis =>
      rw [roundsStep_succ_store]
      intro shape other avoids
      exact (inductionHypothesis _ other avoids).trans
        (IntegerSqrt.roundInto_callerFrame (wideInput refs) refs.round store other avoids)

/-- The actual loop consumes the original remaining interval, without new arithmetic premises. -/
theorem roundsStep_correct (refs : Refs ctx inputWidth) (remaining : Nat)
    (separation : Separation refs) (store : Store ctx)
    (initial : RemainingState remaining refs store) :
    RemainingState 0 refs (roundsStep (model := model) refs remaining store).1 := by
  induction remaining generalizing store with
  | zero => exact initial
  | succ remaining inductionHypothesis =>
      rw [roundsStep_succ_store]
      apply inductionHypothesis
      exact remainingState_after_round refs store _ initial
        (IntegerSqrt.roundStep_correct (wideInput refs) refs.round separation.round store
          (remainingState_roundInitial refs store initial)) separation

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
