/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Deshift
import all QuantumAlg.Util.NumberTheory.SharedEEA.PackingBoundary
import all QuantumAlg.Util.NumberTheory.SharedEEA.ShiftArithmetic

/-!
# Composition of the actual shared-EEA arithmetic phases

Alignment first computes its scale by actual comparisons and doublings.
Division consumes that scale and writes the quotient. The coefficient
phase receives precisely those written bits, and its retained final scale
determines the fourth phase's right shifts
[LYL+26, sec_EEA/sub_regshare.tex:275-315]. No phase is initialized by
computing a quotient in advance.

The actual recorded counts of all four phase calls coincide. Their sum
is therefore four times the proved quotient bit length, as used in
[LYL+26, app_proof/sub_stepnum.tex:4-8]. These are counts of the existing
decoded arithmetic and finite-word microsteps, not native quantum events.
The fourth-phase output is connected to the exact exchanged packed words,
including zero phase/sign/shift and the changed iteration parity.

The original admissible domain supplies the arithmetic inverse laws.
The forward macro coordinates retain enough information for their inverse;
this does not assert erasure of the separately retained forward state Gamma.
Counter placement, a full shared-register quantum gate composition, its
literal native event trace, and the modified terminal circuit remain
separate refinements.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PhaseComposition

/-- Initialize coefficient consumption from the quotient actually written by phases one and two. -/
def coefficientInput (state : IterationState) : CoefficientPhase.State :=
  DivisionPhase.coefficientStart state (Alignment.divide state.remainder state.divisor)

/-- Consume the actual extracted quotient using the existing coefficient microsteps. -/
def coefficientOutput (state : IterationState) : CoefficientPhase.State :=
  CoefficientPhase.finish state.coefficient (coefficientInput state)

/-- Recover the shift coordinate from the actual final binary scale, without discarding it. -/
def retainedShift (state : IterationState) : Nat := (coefficientOutput state).scale.size - 1

/-- Actual extracted bits initialize the same coefficient arithmetic as the macro specification. -/
theorem coefficientInput_eq_start (state : IterationState) (active : 0 < state.divisor) :
    coefficientInput state = CoefficientPhase.start state :=
  DivisionPhase.coefficientStart_divide state _ _
    (Alignment.align_scale state.remainder state.divisor)
    (Alignment.align_stops state.remainder state.divisor active)

/-- The real written-bit coordinate counts exactly the division steps that followed alignment. -/
theorem division_written (state : IterationState) :
    (Alignment.divide state.remainder state.divisor).written =
      (Alignment.align state.remainder state.divisor).places := by
  change (DivisionPhase.run state.divisor
    (Alignment.align state.remainder state.divisor).places
    (DivisionPhase.start state.remainder
      (Alignment.align state.remainder state.divisor).scale)).written = _
  simpa only [DivisionPhase.start, Nat.zero_add] using
    DivisionPhase.run_written state.divisor
      (Alignment.align state.remainder state.divisor).places
      (DivisionPhase.start state.remainder
        (Alignment.align state.remainder state.divisor).scale)

/-- The actual quotient passed to phase three has the preceding phase's actual shift count. -/
theorem coefficientInput_size (state : IterationState) (active : 0 < state.divisor) :
    (coefficientInput state).remaining.size =
      (Alignment.align state.remainder state.divisor).places := by
  rw [coefficientInput_eq_start state active]
  exact (Alignment.align_places_eq_quotient_size state.remainder state.divisor active).symm

/-- The third phase executes exactly the recorded alignment count on the actual extracted bits. -/
theorem coefficientOutput_run (state : IterationState) (active : 0 < state.divisor) :
    coefficientOutput state = CoefficientPhase.run state.coefficient
      (Alignment.align state.remainder state.divisor).places (coefficientInput state) := by
  unfold coefficientOutput CoefficientPhase.finish
  rw [coefficientInput_size state active]

/-- The actual third-phase scale records every consumed quotient bit. -/
theorem coefficientOutput_scale (state : IterationState) (active : 0 < state.divisor) :
    (coefficientOutput state).scale =
      2 ^ (Alignment.align state.remainder state.divisor).places := by
  rw [coefficientOutput_run state active, CoefficientPhase.run_scale]
  change 2 ^ (Alignment.align state.remainder state.divisor).places * 1 = _
  exact Nat.mul_one _

/-- Reading the actual retained scale recovers precisely the fourth phase's required shift count. -/
theorem retainedShift_eq_places (state : IterationState) (active : 0 < state.divisor) :
    retainedShift state = (Alignment.align state.remainder state.divisor).places := by
  rw [retainedShift, coefficientOutput_scale state active, Nat.size_pow, Nat.add_sub_cancel]

/-- Sum the counts read from the actual four phase interfaces. -/
def microsteps (state : IterationState) : Nat :=
  (Alignment.align state.remainder state.divisor).places +
    (Alignment.divide state.remainder state.divisor).written +
    (coefficientInput state).remaining.size + retainedShift state

/-- The four arithmetic/word phase calls account for four times the actual quotient bit length. -/
theorem microsteps_eq_quotient (state : IterationState) (active : 0 < state.divisor) :
    microsteps state = 4 * state.quotient.size := by
  rw [microsteps, division_written, coefficientInput_size state active,
    retainedShift_eq_places state active,
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active]
  change state.quotient.size + state.quotient.size + state.quotient.size + state.quotient.size = _
  omega

/-- Assemble the arithmetic coordinates actually produced by the phase calls and final exchange. -/
def boundary (state : IterationState) : IterationState :=
  ⟨state.divisor, (Alignment.divide state.remainder state.divisor).remainder,
    (coefficientOutput state).value, state.coefficient⟩

/-- The composed arithmetic outputs are exactly the entire next macro state. -/
theorem boundary_eq_step (state : IterationState) (active : 0 < state.divisor) :
    boundary state = IterationState.step state := by
  have coordinates := Alignment.division_coefficient_coordinates state active
  exact congrArg₂ (fun remainder coefficient : Nat =>
    (⟨state.divisor, remainder, coefficient, state.coefficient⟩ : IterationState))
    coordinates.1 coordinates.2

/-- The output macro coordinates recover all four original coordinates on the original domain. -/
theorem boundary_rewind (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) : IterationState.rewind (boundary state) = state := by
  rw [boundary_eq_step state active]
  exact IterationState.rewind_step state valid.coefficient_pos valid.previous_lt

/-- The real retained count reverses every coefficient microstep, recovering the extracted bits. -/
theorem coefficient_rewind (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) :
    CoefficientPhase.rewindRun state.coefficient (retainedShift state)
      (coefficientOutput state) = coefficientInput state := by
  rw [retainedShift_eq_places state active, coefficientOutput_run state active]
  apply CoefficientPhase.rewindRun_run
  rw [coefficientInput_eq_start state active]
  exact CoefficientPhase.start_below state valid

/-- The actual third-phase value is precisely the input used by the established fourth phase. -/
theorem coefficientOutput_value (state : IterationState) (active : 0 < state.divisor) :
    (coefficientOutput state).value = Deshift.phaseValue state := by
  rw [coefficientOutput_run state active, coefficientInput_eq_start state active]
  rfl

/-- Perform the existing fourth phase on the actual third-phase value, word, and retained count. -/
def deshiftOutput (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    Deshift.State (CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size) :=
  Deshift.run state.coefficient (coefficientOutput state).value (retainedShift state)
    (Deshift.start (retainedShift state) iteration
      (CoefficientCapacity.work2Payload state modulus (retainedShift state) valid conserved active))

/-- All actual fourth-phase shifts finish with the exact word and every source control bit. -/
theorem deshiftOutput_spec (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    deshiftOutput state modulus valid conserved active iteration =
      ⟨0, WordRotation.packRotatedWork2 0
        (CoefficientCapacity.work2Payload state modulus (retainedShift state)
          valid conserved active), ⟨false, false, false, !iteration⟩⟩ := by
  unfold deshiftOutput
  rw [retainedShift_eq_places state active, coefficientOutput_value state active]
  exact Deshift.finish_from_coefficient state modulus valid conserved active iteration

private theorem unrotated {coefficientWidth remainderWidth : Nat}
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    WordRotation.packRotatedWork2 0 payload = WordPacking.packWork2 payload := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simp only [WordRotation.packRotatedWork2, BitVec.getMsbD_rotateLeft, Nat.zero_add,
    Nat.mod_eq_of_lt within, within, decide_true, Bool.true_and]

/-- The entire actually deshifted word equals the exact packed boundary word before exchange. -/
theorem deshiftOutput_word (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (deshiftOutput state modulus valid conserved active iteration).word.cast
        (CoefficientCapacity.work2_width state modulus valid conserved) =
      PackingBoundary.completedSecondWord state modulus valid conserved active := by
  rw [deshiftOutput_spec state modulus valid conserved active iteration]
  change (WordRotation.packRotatedWork2 0
    (CoefficientCapacity.work2Payload state modulus (retainedShift state)
      valid conserved active)).cast _ = _
  rw [unrotated, retainedShift_eq_places state active,
    Alignment.align_places_eq_quotient_size state.remainder state.divisor active]
  rfl

/-- The actual deshift result participates in the literal exchange into both next packed words. -/
theorem exchanged_words (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (PackingBoundary.completedFirstWord state modulus valid conserved,
        (deshiftOutput state modulus valid conserved active iteration).word.cast
          (CoefficientCapacity.work2_width state modulus valid conserved)).swap =
      (PackingBoundary.firstWord (IterationState.step state) modulus
          (IterationState.step_admissible state valid active)
          ((IterationState.step_balance state).trans conserved),
        PackingBoundary.secondWord (IterationState.step state) modulus
          (IterationState.step_admissible state valid active)
          ((IterationState.step_balance state).trans conserved)) := by
  rw [deshiftOutput_word state modulus valid conserved active iteration]
  exact PackingBoundary.completed_exchange state modulus valid conserved active

/-- Every actual retained phase count fits both finite counter widths without a caller bound. -/
theorem retainedShift_counter_values (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (BitVec.ofNat modulus.size.size (retainedShift state)).toNat = retainedShift state ∧
      (BitVec.ofNat (modulus.size.size + 2) (retainedShift state)).toNat = retainedShift state := by
  rw [retainedShift_eq_places state active]
  exact ShiftArithmetic.alignment_counter_values state modulus _ valid conserved (Nat.le_refl _)

end QuantumAlg.NumberTheory.SharedEEA.PhaseComposition
