/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Terminal.Boundary
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Macro.Frame

/-!
# Actual boundary cleanup from the reachable Euclidean invariant

The real word exchange and ordered length updates retain the source's
cross-sum and gcd [LYL+26, sec_EEA/sub_regshare.tex:4-23,309-313]. On the
gcd-one trajectory established internally by the original prime input,
the first terminal word is exactly the reversed modulus followed by
`001`. Thus its two actual reused high-clock positions are zero when
divisor length first becomes zero.

These facts discharge the final predicate cleanup of the actual new
boundary program. No high-bit assumption is imposed on an active frame,
and the final zero-divisor transition is included. The gcd premise is an
internal invariant to be supplied by prime-input initialization and its
proved Euclidean preservation, not a new algorithm input restriction.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundaryFrame

noncomputable section

open NumberTheory.SharedEEA MacroBoundary

/-- The complete independent ordered body is the exact next packed macro frame. -/
lemma sourceBody_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    TerminalBoundary.sourceBody (clearedFrame state modulus valid conserved active iteration) =
      frame (IterationState.step state) modulus (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  have lengths := LengthPair.iteration_update state modulus valid conserved active
  apply Registers.ext_fields
  · exact PackingBoundary.completed_second_eq_next_first state modulus valid conserved active
  · exact PackingBoundary.completed_first_eq_next_second state modulus valid conserved active
  · exact congrArg (fun pair : BitVec modulus.size.size × BitVec modulus.size.size => pair.1)
      lengths
  · rfl
  · exact congrArg (fun pair : BitVec modulus.size.size × BitVec modulus.size.size => pair.2)
      lengths
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- An active source boundary uses low zero, regardless of both incoming high bits. -/
lemma condition_clearedFrame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    BoundaryPredicate.condition (clearedFrame state modulus valid conserved active iteration) =
      true := by
  have nonzero :
      (clearedFrame state modulus valid conserved active iteration).divisorLength ≠ 0 := by
    intro zero
    have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) zero
    change (BitVec.ofNat modulus.size.size state.divisor.size).toNat = 0 at value
    rw [NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.divisor modulus
      (Capacity.iteration_fields_le state modulus valid conserved).2.1] at value
    have positive := Nat.size_pos.mpr active
    omega
  rw [BoundaryPredicate.condition_active _ nonzero]
  exact decide_eq_true ⟨rfl, rfl⟩

/-- Every gcd-one macro boundary, including its terminal frame, satisfies the repaired predicate. -/
lemma condition_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1) (iteration : Bool) :
    BoundaryPredicate.condition (frame state modulus valid conserved iteration) = true := by
  apply decide_eq_true
  refine ⟨rfl, rfl, ?_⟩
  by_cases finished : state.divisor = 0
  · right
    have remainder : state.remainder = 1 := by
      simpa only [finished, Nat.gcd_zero_right] using coprime
    have coefficient : state.coefficient = modulus := by
      change state.remainder * state.coefficient +
        state.divisor * state.previousCoefficient = modulus at conserved
      simpa only [remainder, finished, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using conserved
    change PaddingClock.high (PackingBoundary.firstWord state modulus valid conserved) = 0
    rw [TerminalPadding.firstWord_terminal state modulus valid conserved remainder coefficient]
    exact PaddingClock.high_terminalWord modulus
  · left
    intro zero
    have value := frame_divisorLength state modulus valid conserved iteration
    rw [zero] at value
    change 0 = state.divisor.size at value
    have positive := Nat.size_pos.mpr (Nat.pos_of_ne_zero finished)
    omega

/-- The actual new gate sequence reaches the next complete frame and clears its original Ctrl. -/
lemma native_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    TerminalBoundary.step (clearedFrame state modulus valid conserved active iteration) =
      frame (IterationState.step state) modulus (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  have selected := condition_clearedFrame state modulus valid conserved active iteration
  have after : BoundaryPredicate.condition
      (TerminalBoundary.sourceBody
        (clearedFrame state modulus valid conserved active iteration)) = true := by
    rw [sourceBody_frame state modulus valid conserved active iteration]
    exact condition_frame (IterationState.step state) modulus
      (IterationState.step_admissible state valid active)
      ((IterationState.step_balance state).trans conserved)
      ((IterationState.step_gcd state).trans coprime) (!iteration)
  rw [TerminalBoundary.step_selected_clean _ rfl selected after,
    sourceBody_frame state modulus valid conserved active iteration]

end

end QuantumAlg.MAU.Inversion.SharedEEA.TerminalBoundaryFrame
