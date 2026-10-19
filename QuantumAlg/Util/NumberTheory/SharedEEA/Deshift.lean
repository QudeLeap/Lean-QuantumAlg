/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Progress
import all QuantumAlg.Util.NumberTheory.SharedEEA.Phase.Control

/-!
# Actual fourth-phase word shifts and control restoration

Phase four XORs the comparison `t' ≥ 2^ℓ_s * t` into `Sign`, rotates the
second word right once, and decrements its shift count. The same ordered
post-arithmetic control updates then apply
[LYL+26, sec_EEA/sub_regshare.tex:297-315].

The actual completed coefficient phase supplies the comparison bounds.
Its entry sign is one: the first comparison is false, whereas each later
comparison is true. This module retains that distinction, executes the
literal word rotations and the actual Boolean assignments, and proves the
whole fourth phase restores the unrotated word and zero phase/sign bits.
The iteration parity flips exactly at the final boundary.

The initial shift count comes from the actual first-phase alignment. Its
value is also recoverable from the completed coefficient pair; it is not
silently discarded. These are the fourth-phase arithmetic/control laws,
not a complete fixed-schedule EEA circuit or a proof about terminal padding.
The source's subsequent word swap and length refresh remain separate.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.Deshift

variable {width coefficientWidth remainderWidth : Nat}

/-- The actual completed third-phase coefficient, using the recorded alignment count. -/
def phaseValue (state : IterationState) : Nat :=
  (CoefficientPhase.run state.coefficient
    (Alignment.align state.remainder state.divisor).places (CoefficientPhase.start state)).value

/-- The actual third-phase value is the next macro coefficient. -/
lemma phaseValue_eq_next (state : IterationState) (active : 0 < state.divisor) :
    phaseValue state = (IterationState.step state).coefficient := by
  unfold phaseValue
  rw [Alignment.align_places_eq_quotient_size state.remainder state.divisor active]
  exact CoefficientPhase.finish_start_coefficient state

/-- The actual coefficient phase supplies both sides of the fourth-phase comparison boundary. -/
lemma phaseValue_bounds (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) :
    0 < (Alignment.align state.remainder state.divisor).places ∧
      2 ^ ((Alignment.align state.remainder state.divisor).places - 1) * state.coefficient ≤
        phaseValue state ∧
      phaseValue state <
        2 ^ (Alignment.align state.remainder state.divisor).places * state.coefficient := by
  have quotientPositive := IterationState.quotient_pos state valid.divisor_lt active
  have quotientSizePositive := Nat.size_pos.mpr quotientPositive
  have places := Alignment.align_places_eq_quotient_size state.remainder state.divisor active
  change (Alignment.align state.remainder state.divisor).places = state.quotient.size at places
  have placesPositive : 0 < (Alignment.align state.remainder state.divisor).places := by omega
  have highBit : 2 ^ ((Alignment.align state.remainder state.divisor).places - 1) ≤
      state.quotient := Nat.lt_size.mp (by omega)
  refine ⟨placesPositive, ?_, ?_⟩
  · rw [phaseValue_eq_next state active]
    change 2 ^ ((Alignment.align state.remainder state.divisor).places - 1) * state.coefficient ≤
      state.previousCoefficient + state.coefficient * state.quotient
    calc
      _ ≤ state.quotient * state.coefficient := Nat.mul_le_mul_right _ highBit
      _ = state.coefficient * state.quotient := Nat.mul_comm _ _
      _ ≤ _ := Nat.le_add_left _ _
  · have below := CoefficientPhase.run_below state.coefficient
      (Alignment.align state.remainder state.divisor).places (CoefficientPhase.start state)
      (CoefficientPhase.start_below state valid)
    change phaseValue state <
      (CoefficientPhase.run state.coefficient
        (Alignment.align state.remainder state.divisor).places
          (CoefficientPhase.start state)).scale * state.coefficient at below
    simpa only [CoefficientCapacity.current_scale] using below

/-- The completed coefficient pair retains the original actual alignment length. -/
lemma recovered_places (state : IterationState) (valid : state.Admissible)
    (active : 0 < state.divisor) :
    (phaseValue state / state.coefficient).size =
      (Alignment.align state.remainder state.divisor).places := by
  have recovered := IterationState.recoveredQuotient_step state
    valid.coefficient_pos valid.previous_lt
  change (IterationState.step state).coefficient / state.coefficient = state.quotient at recovered
  rw [phaseValue_eq_next state active, recovered]
  exact (Alignment.align_places_eq_quotient_size state.remainder state.divisor active).symm

/-- The source data changed by a fourth-phase microstep. -/
@[ext]
structure State (width : Nat) where
  shift : Nat
  word : BitVec width
  flags : PhaseControl.Flags
deriving DecidableEq

/-- Execute the actual comparison, right rotation, length decrement, and ordered control updates. -/
def step (coefficient value : Nat) (state : State width) : State width :=
  let compared := { state.flags with
    sign := state.flags.sign ^^ decide (2 ^ state.shift * coefficient ≤ value) }
  ⟨state.shift - 1, state.word.rotateRight 1,
    PhaseControl.update true true (decide (state.shift - 1 = 0)) compared⟩

/-- Execute a specified number of the actual fourth-phase microsteps. -/
def run (coefficient value : Nat) : Nat → State width → State width
  | 0, state => state
  | count + 1, state => step coefficient value (run coefficient value count state)

/-- Enter with the actual coefficient-phase control state and retained physical word rotation. -/
def start (places : Nat) (iteration : Bool)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    State (coefficientWidth + remainderWidth) :=
  ⟨places, WordRotation.packRotatedWork2 places payload, ⟨true, true, true, iteration⟩⟩

/-- Closed-form description of the actual intermediate word, length, and all four control bits. -/
def position (places count : Nat) (iteration : Bool)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth) :
    State (coefficientWidth + remainderWidth) :=
  ⟨places - count, WordRotation.packRotatedWork2 (places - count) payload,
    if count = 0 then ⟨true, true, true, iteration⟩
    else ⟨decide (count < places), decide (count < places), false,
      if count = places then !iteration else iteration⟩⟩

/-- The actual comparison combines with the distinct first-step sign to produce sign one. -/
lemma compared_sign (coefficient value places count : Nat)
    (positive : 0 < places) (within : count < places)
    (lower : 2 ^ (places - 1) * coefficient ≤ value)
    (upper : value < 2 ^ places * coefficient) :
    (decide (count = 0) ^^ decide (2 ^ (places - count) * coefficient ≤ value)) = true := by
  by_cases first : count = 0
  · have comparison : ¬ 2 ^ places * coefficient ≤ value := by omega
    simp [first, comparison]
  · have exponentBound : places - count ≤ places - 1 := by omega
    have comparison : 2 ^ (places - count) * coefficient ≤ value :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) exponentBound)).trans
        lower
    simp [first, comparison]

/-- One literal fourth-phase step has exactly the claimed next word, counter, and flags. -/
lemma step_position (coefficient value places count : Nat) (iteration : Bool)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (positive : 0 < places) (beforeEnd : count < places)
    (lower : 2 ^ (places - 1) * coefficient ≤ value)
    (upper : value < 2 ^ places * coefficient) :
    step coefficient value
        ⟨places - count, WordRotation.packRotatedWork2 (places - count) payload,
          ⟨true, true, decide (count = 0), iteration⟩⟩ =
      ⟨places - (count + 1), WordRotation.packRotatedWork2 (places - (count + 1)) payload,
        ⟨decide (count + 1 < places), decide (count + 1 < places), false,
          if count + 1 = places then !iteration else iteration⟩⟩ := by
  apply State.ext
  · change places - count - 1 = places - (count + 1)
    omega
  · change (WordRotation.packRotatedWork2 (places - count) payload).rotateRight 1 =
      WordRotation.packRotatedWork2 (places - (count + 1)) payload
    have displacement : places - count = (places - (count + 1)) + 1 := by omega
    rw [displacement]
    exact WordRotation.packRotatedWork2_unshift _ _
  · change PhaseControl.update true true (decide (places - count - 1 = 0))
      ⟨true, true,
        decide (count = 0) ^^ decide (2 ^ (places - count) * coefficient ≤ value), iteration⟩ = _
    rw [compared_sign coefficient value places count positive beforeEnd lower upper,
      PhaseControl.deshift_transition]
    by_cases finished : count + 1 = places
    · have shiftZero : places - count - 1 = 0 := by omega
      simp [finished, shiftZero]
    · have shiftNonzero : places - count - 1 ≠ 0 := by omega
      have before : count + 1 < places := by omega
      simp [finished, shiftNonzero, before]

/-- The actual fourth-phase run realizes its complete word, length, and flag characterization. -/
lemma run_position (coefficient value places count : Nat) (iteration : Bool)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (positive : 0 < places) (within : count ≤ places)
    (lower : 2 ^ (places - 1) * coefficient ≤ value)
    (upper : value < 2 ^ places * coefficient) :
    run coefficient value count (start places iteration payload) =
      position places count iteration payload := by
  revert within
  induction count with
  | zero =>
    intro _
    simp [run, start, position]
  | succ count inductionHypothesis =>
    intro within
    have beforeEnd : count < places := by omega
    have intermediate : position places count iteration payload =
        ⟨places - count, WordRotation.packRotatedWork2 (places - count) payload,
          ⟨true, true, decide (count = 0), iteration⟩⟩ := by
      by_cases first : count = 0
      · simp [position, first]
      · simp [position, first, beforeEnd, Nat.ne_of_lt beforeEnd]
    rw [run, inductionHypothesis (by omega), intermediate]
    simpa only [position, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false] using
      step_position coefficient value places count iteration payload positive beforeEnd lower upper

/-- After all real shifts, the word is unrotated and the source phase/sign bits are zero. -/
lemma run_finish (coefficient value places : Nat) (iteration : Bool)
    (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (positive : 0 < places)
    (lower : 2 ^ (places - 1) * coefficient ≤ value)
    (upper : value < 2 ^ places * coefficient) :
    run coefficient value places (start places iteration payload) =
      ⟨0, WordRotation.packRotatedWork2 0 payload, ⟨false, false, false, !iteration⟩⟩ := by
  simpa only [position, Nat.sub_self, if_neg (Nat.ne_of_gt positive), Nat.lt_irrefl,
    decide_false, if_true] using
    run_position coefficient value places places iteration payload positive le_rfl lower upper

/-- The fourth phase restores the actual bounded shared word produced by the third phase. -/
lemma finish_from_coefficient (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    let places := (Alignment.align state.remainder state.divisor).places
    let payload := CoefficientCapacity.work2Payload state modulus places valid conserved active
    run state.coefficient (phaseValue state) places (start places iteration payload) =
      ⟨0, WordRotation.packRotatedWork2 0 payload, ⟨false, false, false, !iteration⟩⟩ := by
  obtain ⟨positive, lower, upper⟩ := phaseValue_bounds state valid active
  exact run_finish _ _ _ _ _ positive lower upper

end QuantumAlg.NumberTheory.SharedEEA.Deshift
