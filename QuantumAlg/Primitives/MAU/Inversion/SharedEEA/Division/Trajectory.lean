/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Division.Entry
import Mathlib.Logic.Function.Iterate

/-!
# Exact full-frame trajectory of the actual native division phase

Starting at the alignment output rotation, every actual native microstep
writes one quotient digit and decreases the actual retained shift. After
exactly the count produced by the real first-phase alignment, the same
native microstep sequence enters phase three with the complete written
quotient, Euclidean remainder, unrotated Work2, and cleared Sign
[LYL+26, sec_EEA/sub_regshare.tex:279-288].

Iteration below means ordinary mathematical iteration of the existing
`NativeMicrostep.step`, whose native realization is already certified.
There is no additional interpreter or gate-cost formula. The alignment
count is not initialized by precomputing a quotient. The all-field frame
is an internal reachable basis specification; arbitrary Iter is retained.
Native phase-one arrival and subsequent phases remain separate refinements.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.DivisionTrajectory

noncomputable section

open NumberTheory.SharedEEA

private theorem count_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    count < 2 ^ modulus.size.size :=
  (within.trans (RemainderPhaseFrame.alignment_le state modulus valid conserved)).trans_lt
    (Nat.lt_size_self modulus.size)

/-- Full basis frame after a bounded number of actually executed division microsteps. -/
def phaseFrame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) : Registers modulus.size where
  firstWord := (WordPacking.packWork1
    (DivisionCapacity.work1Payload state modulus count valid conserved active within)).cast
      (DivisionCapacity.work1_width state modulus count valid conserved active within)
  secondWord := (WordRotation.packRotatedWork2
    ((Alignment.align state.remainder state.divisor).places - count)
      (DivisionCapacity.work2Payload state modulus valid conserved)).cast
        (DivisionCapacity.work2_width state modulus valid conserved)
  coefficientLength := BitVec.ofNatLT state.coefficient.size
    (RemainderPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.2.1)
  quotientLength := BitVec.ofNatLT count (count_fits state modulus count valid conserved within)
  divisorLength := BitVec.ofNatLT state.divisor.size
    (RemainderPhaseFrame.size_fits_counter
      (Capacity.iteration_fields_le state modulus valid conserved).2.1)
  shift := BitVec.ofNatLT ((Alignment.align state.remainder state.divisor).places - count)
    (DivisionEntry.original_shift_fits state modulus count valid conserved)
  flags := ⟨decide (count = (Alignment.align state.remainder state.divisor).places),
    !decide (count = (Alignment.align state.remainder state.divisor).places), false, iteration⟩
  control := false

private theorem frame_eq_entry (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    phaseFrame state modulus count valid conserved active beforeEnd.le iteration =
      DivisionEntry.entryFrame state modulus count valid conserved active beforeEnd iteration := by
  unfold phaseFrame
  rw [decide_eq_false (Nat.ne_of_lt beforeEnd)]
  rfl

private theorem next_eq_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    let expected := DivisionAdvance.nextFrame state modulus count
      valid conserved active beforeEnd iteration
    { expected with flags :=
      ⟨decide (expected.shift = (0#modulus.size.size)),
        !decide (expected.shift = (0#modulus.size.size)), false, iteration⟩ } =
      phaseFrame state modulus (count + 1) valid conserved active (by omega) iteration := by
  dsimp only
  let expected := DivisionAdvance.nextFrame state modulus count
    valid conserved active beforeEnd iteration
  have zero : expected.shift = (0#modulus.size.size) ↔
      count + 1 = (Alignment.align state.remainder state.divisor).places := by
    constructor
    · intro same
      have value := congrArg (fun word : BitVec modulus.size.size => word.toNat) same
      change (Alignment.align state.remainder state.divisor).places - (count + 1) = 0 at value
      omega
    · intro atEnd
      apply BitVec.eq_of_toNat_eq
      change (Alignment.align state.remainder state.divisor).places - (count + 1) = 0
      omega
  have test : decide (expected.shift = (0#modulus.size.size)) =
      decide (count + 1 = (Alignment.align state.remainder state.divisor).places) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using zero
  change { expected with flags :=
    ⟨decide (expected.shift = (0#modulus.size.size)),
      !decide (expected.shift = (0#modulus.size.size)), false, iteration⟩ } = _
  rw [test]
  rfl

/-- The same actual complete microstep advances the phase frame at every reachable position. -/
theorem microstep_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    NativeMicrostep.step modulus.size
      (phaseFrame state modulus count valid conserved active beforeEnd.le iteration) =
      phaseFrame state modulus (count + 1) valid conserved active (by omega) iteration := by
  rw [frame_eq_entry state modulus count valid conserved active beforeEnd iteration,
    DivisionEntry.microstep_frame state modulus count valid conserved active beforeEnd iteration]
  exact next_eq_frame state modulus count valid conserved active beforeEnd iteration

/-- Every bounded iteration of the actual native microstep has the stated complete packed frame. -/
theorem iterate_frame (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places)
    (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[count]
      (phaseFrame state modulus 0 valid conserved active (Nat.zero_le _) iteration) =
      phaseFrame state modulus count valid conserved active within iteration := by
  revert within
  induction count with
  | zero =>
      intro within
      rfl
  | succ count ih =>
      intro within
      have previous : count ≤ (Alignment.align state.remainder state.divisor).places := by omega
      rw [Function.iterate_succ_apply', ih previous]
      exact microstep_frame state modulus count valid conserved active (by omega) iteration

/-- The real alignment count reaches the complete coefficient-phase entry. -/
theorem finish_frame (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) (iteration : Bool) :
    (NativeMicrostep.step modulus.size)^[
        (Alignment.align state.remainder state.divisor).places]
      (phaseFrame state modulus 0 valid conserved active (Nat.zero_le _) iteration) =
      phaseFrame state modulus (Alignment.align state.remainder state.divisor).places
        valid conserved active le_rfl iteration :=
  iterate_frame state modulus _ valid conserved active le_rfl iteration

end

end QuantumAlg.MAU.Inversion.SharedEEA.DivisionTrajectory
