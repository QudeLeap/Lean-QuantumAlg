/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Correctness
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Correctness

/-!
# Exact natural square root in the actual caller-visible output

Positive input width is the original domain. Initialization establishes its
own work values, refinement proves the final unit interval, and the final
native copy writes that interval's lower endpoint into the caller output.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Caller reads outside the actual widened-input, round and output write identities. -/
def IntoCallerFrame (refs : Refs ctx inputWidth) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.wideInput.key ∉ other.storageKeys →
      (∀ cell, IntegerSqrt.writeKey refs.round cell ∉ other.storageKeys) →
        refs.output.key ∉ other.storageKeys → after.read other = before.read other

/-- Exact caller-visible result and complete frame of the actual natural-square-root driver. -/
structure Outcome (refs : Refs ctx inputWidth) (before after : Store ctx) : Prop where
  output : (after.read (writeInput refs.output)).toNat = Nat.sqrt (before.read refs.input).toNat
  callerFrame : IntoCallerFrame refs before after

/-- Actual initialization supplies precisely the original remaining-round interval. -/
theorem remainingState_of_init (refs : Refs ctx inputWidth) (positive : 0 < inputWidth)
    (before after : Store ctx) (holds : InitOutcome refs before after) :
    RemainingState inputWidth refs after := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [if_neg (Nat.ne_of_gt positive)]
    exact holds.half
  · rw [holds.root]
    exact Nat.zero_le _
  · rw [holds.wide, holds.root]
    simp only [Nat.zero_add]
    have inputFits := (before.read refs.input).toNat_lt
    have powerLeSquare : 2 ^ inputWidth ≤ 2 ^ inputWidth * 2 ^ inputWidth :=
      Nat.le_mul_of_pos_left _ (by positivity : 0 < 2 ^ inputWidth)
    exact inputFits.trans_le powerLeSquare
  · rw [holds.root]
    simpa only [Nat.zero_add, CShape.wordModulus, workWidth] using Nat.le_refl (2 ^ inputWidth)

/-- Every actual caller read outside the driver's writes is preserved without value premises. -/
theorem into_callerFrame (refs : Refs ctx inputWidth) (store : Store ctx) :
    IntoCallerFrame refs store (step refs store).1 := by
  intro shape other avoidsWide avoidsRound avoidsOutput
  rw [step_store, Store.read_applyOp_of_not_mem_storageKeys _ (finishOp refs) other avoidsOutput]
  exact (roundsStep_callerFrame refs inputWidth _ other avoidsRound).trans
    (initializeInto_callerFrame refs store other avoidsWide
      (avoidsRound .root) (avoidsRound .half))

/-- The actual finite driver writes Nat.sqrt of the original input into the caller output. -/
theorem step_correct (refs : Refs ctx inputWidth) (separation : Separation refs)
    (positive : 0 < inputWidth) (store : Store ctx) :
    Outcome refs store (step refs store).1 := by
  have initialized := initializeInto_correct refs separation positive store
  have finalInterval := roundsStep_correct refs inputWidth separation _
    (remainingState_of_init refs positive store _ initialized)
  have rootSqrt := remainingState_zero_root_eq_sqrt refs _ finalInterval
  have wideFrame := roundsStep_callerFrame refs inputWidth (initializeStep refs store).1
    (wideInput refs) separation.round.1
  refine ⟨?_, into_callerFrame refs store⟩
  rw [step_store]
  change (((roundsStep refs inputWidth (initializeStep refs store).1).1.applyOp
    (finishOp refs)).read
    (.storage (finishOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change ((roundsStep refs inputWidth (initializeStep refs store).1).1.read
    (writeInput refs.round.root)).toNat = _
  rw [rootSqrt, wideFrame, initialized.wide]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
