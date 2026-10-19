/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Deshift.Advance
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Macro.Boundary
import Mathlib.Logic.Function.Iterate

/-!
# Actual full fourth-phase trajectory through the real macro exchange

Every iteration below applies the already realized eight-block native
microstep. The full aligned comparison gives the correct Sign; the real
right shifts then remove the retained rotation one bit at a time. At zero
shift the program really complements the two phase bits, swaps both work
words, refreshes both finite lengths, and flips Iter
[LYL+26, sec_EEA/sub_regshare.tex:297-313;
LYL+26, sec_EEA/sub_opt.tex:61-84].

The result is the complete next macro-state basis frame, including a zero
next divisor. This is not a claim that subsequent terminal padding is idle
or that the original low counter implements a repaired terminal schedule.
The first-phase alignment and the bounded terminal forward/inverse gate
integration remain separate actual-program obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DeshiftTrajectory

noncomputable section

open NumberTheory.SharedEEA DeshiftPhaseFrame

private lemma frame_shift_eq (state : IterationState) (modulus left right : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (leftWithin : left ≤ state.quotient.size)
    (rightWithin : right ≤ state.quotient.size) (same : left = right) (sign iteration : Bool) :
    frame state modulus left valid conserved active leftWithin sign iteration =
      frame state modulus right valid conserved active rightWithin sign iteration := by
  cases same
  rfl

/-- Mathematical full-frame description of each position of the same actual deshift program. -/
def position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) : Registers modulus.size :=
  if count < state.quotient.size then
    frame state modulus (state.quotient.size - count) valid conserved active
      (Nat.sub_le _ _) (decide (count = 0)) iteration
  else
    MacroBoundary.frame (IterationState.step state) modulus
      (IterationState.step_admissible state valid active)
      ((IterationState.step_balance state).trans conserved) (!iteration)

private lemma last_microstep (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size)
    (last : count + 1 = state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (frame state modulus (state.quotient.size - count) valid conserved active
        (Nat.sub_le _ _) (decide (count = 0)) iteration) =
      MacroBoundary.frame (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  let original := frame state modulus (state.quotient.size - count) valid conserved active
    (Nat.sub_le _ _) (decide (count = 0)) iteration
  have after : frame state modulus (state.quotient.size - count - 1) valid conserved active
      ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) false iteration =
      frame state modulus 0 valid conserved active (Nat.zero_le _) false iteration :=
    frame_shift_eq state modulus _ _ valid conserved active _ _ (by omega) false iteration
  rw [NativeMicrostep.step,
    CoefficientTail.pre_shift_inactive modulus.size original rfl rfl,
    CoefficientTail.remainder_inactive modulus.size original rfl rfl,
    DeshiftPhasePrelude.quotient_inactive modulus.size original rfl rfl,
    DeshiftAdvance.native_shift_control state modulus count
      valid conserved active beforeEnd iteration, after]
  exact MacroBoundary.deshift_tail_frame state modulus valid conserved coprime active iteration

/-- One complete actual native microstep advances each active position, including the exchange. -/
lemma microstep_position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (position state modulus count valid conserved active iteration) =
      position state modulus (count + 1) valid conserved active iteration := by
  unfold position
  rw [if_pos beforeEnd]
  by_cases notLast : count + 1 < state.quotient.size
  · rw [if_pos notLast, DeshiftAdvance.microstep_frame state modulus count
      valid conserved active notLast iteration, decide_eq_false (by omega : count + 1 ≠ 0)]
    exact frame_shift_eq state modulus _ _ valid conserved active _ _ (by omega) false iteration
  · rw [if_neg notLast]
    exact last_microstep state modulus count valid conserved coprime active
      beforeEnd (by omega) iteration

/-- The ordinary iterate of the actual native action has the complete specified physical frame. -/
lemma iterate_position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[count]
      (frame state modulus state.quotient.size valid conserved active le_rfl true iteration) =
      position state modulus count valid conserved active iteration := by
  revert within
  induction count with
  | zero =>
      intro _
      have positive := Nat.size_pos.mpr
        (IterationState.quotient_pos state valid.divisor_lt active)
      rw [Function.iterate_zero_apply, position, if_pos positive]
      rfl
  | succ count ih =>
      intro within
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact microstep_position state modulus count
        valid conserved coprime active (by omega) iteration

/-- Full actual deshifting ends at the next macro frame with exact lengths and flipped Iter. -/
lemma finish_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (coprime : Nat.gcd state.remainder state.divisor = 1)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[state.quotient.size]
      (CoefficientTrajectory.phaseFrame state modulus state.quotient.size
        valid conserved active le_rfl iteration) =
      MacroBoundary.frame (IterationState.step state) modulus
        (IterationState.step_admissible state valid active)
        ((IterationState.step_balance state).trans conserved) (!iteration) := by
  rw [DeshiftComparison.entry_frame state modulus valid conserved active iteration,
    iterate_position state modulus state.quotient.size
      valid conserved coprime active le_rfl iteration,
    position, if_neg (Nat.lt_irrefl _)]

end

end QuantumAlg.MAU.Inversion.SharedEEA.DeshiftTrajectory
