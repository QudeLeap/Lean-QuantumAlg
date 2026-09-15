/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Layout
import Mathlib.Data.Nat.Sqrt

/-!
# The original binary-refinement interval on actual stores

The interval is independent of the interpreter record. One round's proved
actual outcome advances it, and the final unit interval characterizes Nat.sqrt.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

/-- Search invariant before the remaining refinement rounds. -/
structure RemainingState {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {inputWidth : Nat} (remaining : Nat) (refs : Refs ctx inputWidth)
    (observation : Store ctx) : Prop where
  half : (observation.read (writeInput refs.round.half)).toNat =
    if remaining = 0 then 0 else 2 ^ (remaining - 1)
  lower :
    (observation.read (writeInput refs.round.root)).toNat *
        (observation.read (writeInput refs.round.root)).toNat ≤
      (observation.read (wideInput refs)).toNat
  upper :
    (observation.read (wideInput refs)).toNat <
      ((observation.read (writeInput refs.round.root)).toNat + 2 ^ remaining) *
        ((observation.read (writeInput refs.round.root)).toNat + 2 ^ remaining)
  bounded :
    (observation.read (writeInput refs.round.root)).toNat + 2 ^ remaining ≤
      CShape.wordModulus (workWidth inputWidth)

/-- A nonempty search state supplies the exact one-round precondition. -/
theorem remainingState_roundInitial {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {inputWidth remaining : Nat}
    (refs : Refs ctx inputWidth) (observation : Store ctx)
    (state : RemainingState (remaining + 1) refs observation) :
    IntegerSqrt.RoundInitial (wideInput refs) refs.round observation := by
  have halfValue :
      (observation.read (writeInput refs.round.half)).toNat = 2 ^ remaining := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel] using state.half
  have powerStrict : 2 ^ remaining < 2 ^ (remaining + 1) :=
    Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self remaining)
  have midpointFits :
      (observation.read (writeInput refs.round.root)).toNat +
          (observation.read (writeInput refs.round.half)).toNat <
        CShape.wordModulus (workWidth inputWidth) := by
    rw [halfValue]
    have bounded := state.bounded
    omega
  refine ⟨midpointFits, state.lower, ?_⟩
  rw [halfValue]
  have doubledPower : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [pow_succ]
    omega
  have upper := state.upper
  rw [doubledPower] at upper
  simpa only [Nat.add_assoc] using upper

/-- One exact refinement advances the remaining-round invariant. -/
theorem remainingState_after_round {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {inputWidth remaining : Nat}
    (refs : Refs ctx inputWidth) (before after : Store ctx)
    (state : RemainingState (remaining + 1) refs before)
    (holds : IntegerSqrt.RoundOutcome (wideInput refs) refs.round before after)
    (separation : Separation refs) : RemainingState remaining refs after := by
  have halfBefore :
      (before.read (writeInput refs.round.half)).toNat = 2 ^ remaining := by
    simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
      Nat.add_sub_cancel] using state.half
  have inputFrame : after.read (wideInput refs) = before.read (wideInput refs) :=
    holds.callerFrame (wideInput refs) separation.round.1
  have halfAfter :
      (after.read (writeInput refs.round.half)).toNat =
        if remaining = 0 then 0 else 2 ^ (remaining - 1) := by
    rw [holds.half, halfBefore]
    cases remaining with
    | zero => rfl
    | succ remaining =>
        simp only [if_false, Nat.succ_ne_zero, pow_succ, Nat.add_sub_cancel]
        exact Nat.mul_div_left _ (by decide : 0 < 2)
  have lowerAfter :
      (after.read (writeInput refs.round.root)).toNat *
          (after.read (writeInput refs.round.root)).toNat ≤
        (after.read (wideInput refs)).toNat := by
    rw [inputFrame]
    exact holds.lower
  have upperAfter :
      (after.read (wideInput refs)).toNat <
        ((after.read (writeInput refs.round.root)).toNat + 2 ^ remaining) *
          ((after.read (writeInput refs.round.root)).toNat + 2 ^ remaining) := by
    rw [inputFrame, ← halfBefore]
    exact holds.upper
  have doubledPower : 2 ^ (remaining + 1) = 2 ^ remaining + 2 ^ remaining := by
    rw [pow_succ]
    omega
  have boundedAfter :
      (after.read (writeInput refs.round.root)).toNat + 2 ^ remaining ≤
        CShape.wordModulus (workWidth inputWidth) := by
    have rootValue := holds.root
    unfold IntegerSqrt.selectedRoot at rootValue
    by_cases selected :
        IntegerSqrt.midpoint refs.round before * IntegerSqrt.midpoint refs.round before ≤
          (before.read (wideInput refs)).toNat
    · rw [if_pos selected] at rootValue
      unfold IntegerSqrt.midpoint at rootValue
      change (after.read (writeInput refs.round.root)).toNat =
        (before.read (writeInput refs.round.root)).toNat +
          (before.read (writeInput refs.round.half)).toNat at rootValue
      have bounded := state.bounded
      rw [rootValue, halfBefore]
      rw [doubledPower] at bounded
      omega
    · rw [if_neg selected] at rootValue
      change (after.read (writeInput refs.round.root)).toNat =
        (before.read (writeInput refs.round.root)).toNat at rootValue
      have bounded := state.bounded
      rw [rootValue]
      rw [doubledPower] at bounded
      omega
  exact ⟨halfAfter, lowerAfter, upperAfter, boundedAfter⟩

/-- The final search interval characterizes the natural square root. -/
theorem remainingState_zero_root_eq_sqrt {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {inputWidth : Nat} (refs : Refs ctx inputWidth)
    (observation : Store ctx)
    (state : RemainingState 0 refs observation) :
    (observation.read (writeInput refs.round.root)).toNat =
      Nat.sqrt (observation.read (wideInput refs)).toNat := by
  apply Nat.eq_sqrt.mpr
  refine ⟨state.lower, ?_⟩
  simpa only [pow_zero, Nat.add_one] using state.upper

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
