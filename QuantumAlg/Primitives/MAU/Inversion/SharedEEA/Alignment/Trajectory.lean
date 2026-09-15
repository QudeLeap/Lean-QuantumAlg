/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Alignment.Advance
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Trajectory
import all QuantumAlg.Util.NumberTheory.SharedEEA.Alignment.Test
import Mathlib.Logic.Function.Iterate

/-!
# Full actual first-phase trajectory from zero shift to division

The first native step starts at the unchanged macro frame with shift zero.
Every actual step rotates the old second work word, increments the retained
counter, compares at that new scale, and writes the result through Sign
into Phase2 [LYL+26, sec_EEA/sub_regshare.tex:275-287;
LYL+26, sec_EEA/sub_opt.tex:37-79]. The terminal frame is exactly the input
of the already realized native division trajectory.

The quotient-size expression is the proved length of those real shifts,
not an input-dependent initial preparation or a separate stopping oracle.
All whole words, finite counters, phase bits, Sign, arbitrary Iter, and
Ctrl are matched. The underlying input domain and possible external
correlations are unchanged by these complete basis-action identities.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.AlignmentTrajectory

noncomputable section

open NumberTheory.SharedEEA AlignmentPhaseFrame

/-- Complete physical description after the stated number of actually executed alignment steps. -/
def position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : count ≤ state.quotient.size) (iteration : Bool) : Registers modulus.size :=
  { frame state modulus count valid conserved within false iteration with
    flags := ⟨false, decide (count = state.quotient.size), false, iteration⟩ }

private theorem before_eq_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    position state modulus count valid conserved beforeEnd.le iteration =
      frame state modulus count valid conserved beforeEnd.le false iteration := by
  unfold position
  rw [decide_eq_false (Nat.ne_of_lt beforeEnd)]
  rfl

/-- The actual native comparison controls the precise first transition into division. -/
theorem microstep_position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (beforeEnd : count < state.quotient.size) (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (position state modulus count valid conserved beforeEnd.le iteration) =
      position state modulus (count + 1) valid conserved (by omega) iteration := by
  rw [before_eq_frame state modulus count valid conserved beforeEnd iteration,
    AlignmentAdvance.microstep_frame state modulus count valid conserved active beforeEnd iteration,
    AlignmentTest.decide_comparison state (count + 1) active (by omega)]
  rfl

/-- The actual macro boundary supplies shift zero without preparing any quotient-dependent value. -/
theorem initial_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) (iteration : Bool) :
    MacroBoundary.frame state modulus valid conserved iteration =
      frame state modulus 0 valid conserved (Nat.zero_le _) false iteration := by
  apply Registers.ext_fields
  · rfl
  · exact (congrArg
      (fun word : BitVec (CoefficientCapacity.work2CoefficientWidth state modulus +
          state.divisor.size) => word.cast
        (DivisionCapacity.work2_width state modulus valid conserved))
      (TerminalTail.rotateLeft_zero _)).symm
  · apply BitVec.eq_of_toNat_eq
    exact NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.coefficient modulus
      (Capacity.iteration_fields_le state modulus valid conserved).2.2.1
  · rfl
  · apply BitVec.eq_of_toNat_eq
    exact NumberTheory.SharedEEA.LengthRefresh.encoded_length_toNat state.divisor modulus
      (Capacity.iteration_fields_le state modulus valid conserved).2.1
  · apply BitVec.eq_of_toNat_eq
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Iterating the actual eight-block action from its zero-shift macro input reaches every frame. -/
theorem iterate_position (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (within : count ≤ state.quotient.size) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[count] (MacroBoundary.frame state modulus
      valid conserved iteration) =
        position state modulus count valid conserved within iteration := by
  revert within
  induction count with
  | zero =>
      intro _
      have positive := Nat.size_pos.mpr
        (IterationState.quotient_pos state valid.divisor_lt active)
      rw [Function.iterate_zero_apply,
        before_eq_frame state modulus 0 valid conserved positive iteration]
      exact initial_frame state modulus valid conserved iteration
  | succ count ih =>
      intro within
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact microstep_position state modulus count valid conserved active (by omega) iteration

/-- The last real comparison leaves exactly the complete initial frame of native division. -/
theorem division_entry (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    position state modulus state.quotient.size valid conserved le_rfl iteration =
      DivisionTrajectory.phaseFrame state modulus 0 valid conserved active (Nat.zero_le _)
        iteration := by
  have places := Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  change (Alignment.align state.remainder state.divisor).places = state.quotient.size at places
  have positive : 0 < (Alignment.align state.remainder state.divisor).places := by
    rw [places]
    exact Nat.size_pos.mpr (IterationState.quotient_pos state valid.divisor_lt active)
  apply Registers.ext_fields
  · rfl
  · exact congrArg
      (fun shift => (WordRotation.packRotatedWork2 shift
        (DivisionCapacity.work2Payload state modulus valid conserved)).cast
          (DivisionCapacity.work2_width state modulus valid conserved)) places.symm
  · rfl
  · apply BitVec.eq_of_toNat_eq
    rfl
  · rfl
  · apply BitVec.eq_of_toNat_eq
    exact places.symm
  · change false = decide (0 = (Alignment.align state.remainder state.divisor).places)
    exact (decide_eq_false (by omega)).symm
  · change decide (state.quotient.size = state.quotient.size) =
      !decide (0 = (Alignment.align state.remainder state.divisor).places)
    rw [decide_eq_true rfl, decide_eq_false (by omega), Bool.not_false]
  · rfl
  · rfl
  · rfl

/-- Complete alignment feeds the same native division trajectory on the entire original frame. -/
theorem finish_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[state.quotient.size]
      (MacroBoundary.frame state modulus valid conserved iteration) =
      DivisionTrajectory.phaseFrame state modulus 0 valid conserved active (Nat.zero_le _)
        iteration := by
  rw [iterate_position state modulus state.quotient.size valid conserved active le_rfl iteration,
    division_entry state modulus valid conserved active iteration]

end

end QuantumAlg.MAU.Inversion.SharedEEA.AlignmentTrajectory
