/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Word.Rotation
import all QuantumAlg.Util.NumberTheory.SharedEEA.Phase.Control

/-!
# Actual terminal alignment tail with a finite shift register

The source enters phase `00` after the terminal word exchange. A zero
divisor disables the first post-arithmetic phase update, but does not
disable the preceding left shift or finite shift-register increment
[LYL+26, sec_EEA/sub_opt.tex:37-48,74-84]. The zero-shift test, whole-word
swap, and iteration-parity toggle still apply. The length registers have
the stated finite width [LYL+26, sec_EEA/sub_regshare.tex:22-23].

This owner projects that actual zero-divisor alignment branch onto the
two work words, shift register, and control bits. Addition and subtraction
of the zero divisor preserve their selected arithmetic window. The source
length-refresh circuit is not redefined here: no values of the other
length registers are inferred after an overflow-triggered exchange.

Before the first finite-counter wrap, every preceding state remains in
phase `00`, and the word rotates while the retained shift records the
displacement. At the first wrap, the actual control test triggers phase
`11` and a whole-word exchange. The restricted branch recurrence is not
asserted to describe later source steps. This proves neither idle padding
nor erasure of the forward state `Γ`; the retained shift instead gives
the exact inverse rotation before wrap
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128].
-/

namespace QuantumAlg.NumberTheory.SharedEEA.TerminalTail

variable {wordWidth clockWidth : Nat}

private lemma literal_zero (width : Nat) : BitVec.ofNat width 0 = (0 : BitVec width) := by
  apply BitVec.eq_of_toNat_eq
  change 0 % 2 ^ width = 0
  exact Nat.zero_mod _

/-- The finite shift increment has its actual modular value, including a zero-bit register. -/
lemma increment_toNat (shift : BitVec clockWidth) :
    (shift + 1).toNat = (shift.toNat + 1) % 2 ^ clockWidth := by
  change (shift.toNat + 1 % 2 ^ clockWidth) % 2 ^ clockWidth = _
  exact Nat.add_mod_mod _ _ _

/-- Literal finite addition advances the encoded natural count modulo the register capacity. -/
lemma increment_ofNat (count : Nat) :
    BitVec.ofNat clockWidth count + 1 = BitVec.ofNat clockWidth (count + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [increment_toNat]
  change (count % 2 ^ clockWidth + 1) % 2 ^ clockWidth =
    (count + 1) % 2 ^ clockWidth
  exact Nat.mod_add_mod _ _ _

private lemma ofNat_nonzero (count : Nat) (positive : 0 < count)
    (within : count < 2 ^ clockWidth) : BitVec.ofNat clockWidth count ≠ 0 := by
  intro zero
  have values := congrArg BitVec.toNat zero
  change count % 2 ^ clockWidth = 0 at values
  rw [Nat.mod_eq_of_lt within] at values
  omega

/-- The first complete finite-counter period is detected as zero by the actual register. -/
lemma first_wrap_zero : BitVec.ofNat clockWidth (2 ^ clockWidth) = 0 := by
  apply BitVec.eq_of_toNat_eq
  change 2 ^ clockWidth % 2 ^ clockWidth = 0
  exact Nat.mod_self _

/-- The zero divisor changes neither operand of the actual subtract-and-add-back arithmetic. -/
lemma zero_arithmetic (word : BitVec wordWidth) : (word - 0) + 0 = word := by
  calc
    _ = (word - BitVec.ofNat wordWidth 0) + BitVec.ofNat wordWidth 0 := by rw [literal_zero]
    _ = word :=
      (congrArg (fun value => value + BitVec.ofNat wordWidth 0) (BitVec.sub_zero word)).trans
        (BitVec.add_zero word)

/-- With zero divisor, only the actual zero-shift test changes phase and iteration parity. -/
lemma zero_divisor_control (shiftZero iteration : Bool) :
    PhaseControl.update true false shiftZero ⟨false, false, false, iteration⟩ =
      ⟨shiftZero, shiftZero, false, if shiftZero then !iteration else iteration⟩ := by
  cases shiftZero <;> cases iteration <;> decide

/-- The source coordinates tracked through its zero-divisor alignment branch. -/
@[ext]
structure Frame (wordWidth clockWidth : Nat) where
  firstWord : BitVec wordWidth
  secondWord : BitVec wordWidth
  shift : BitVec clockWidth
  flags : PhaseControl.Flags
deriving DecidableEq

/-- Actual terminal alignment instructions, including tracked exchange and parity. -/
def alignmentPrefix (state : Frame wordWidth clockWidth) : Frame wordWidth clockWidth :=
  let shifted := state.secondWord.rotateLeft 1
  let advanced := state.shift + 1
  let shiftZero := decide (advanced = 0)
  ⟨if shiftZero then shifted else state.firstWord,
    if shiftZero then state.firstWord else shifted,
    advanced, PhaseControl.update true false shiftZero state.flags⟩

/-- Reverse those same tracked assignments using the actual post-increment zero predicate. -/
def rewindPrefix (state : Frame wordWidth clockWidth) : Frame wordWidth clockWidth :=
  let shiftZero := decide (state.shift = 0)
  let first := if shiftZero then state.secondWord else state.firstWord
  let second := if shiftZero then state.firstWord else state.secondWord
  ⟨first, second.rotateRight 1, state.shift - 1,
    PhaseControl.rewind true false shiftZero state.flags⟩

/-- Neither the finite increment, conditional exchange, nor ordered flags lose tracked data. -/
lemma rewind_alignmentPrefix (state : Frame wordWidth clockWidth) :
    rewindPrefix (alignmentPrefix state) = state := by
  cases predicate : decide (state.shift + 1 = 0) <;>
    simp only [alignmentPrefix, rewindPrefix, predicate, Bool.false_eq_true, if_false, if_true,
      WordRotation.rotateRight_rotateLeft, BitVec.add_sub_cancel, PhaseControl.rewind_update]

/-- The restricted terminal branch is injective on its tracked finite coordinates. -/
lemma alignmentPrefix_injective :
    Function.Injective (alignmentPrefix (wordWidth := wordWidth) (clockWidth := clockWidth)) := by
  intro left right same
  calc
    left = rewindPrefix (alignmentPrefix left) := (rewind_alignmentPrefix left).symm
    _ = rewindPrefix (alignmentPrefix right) := congrArg rewindPrefix same
    _ = right := rewind_alignmentPrefix right

/-- Begin at the actual unrotated terminal boundary with zero phase and sign bits. -/
def start (first second : BitVec wordWidth) (iteration : Bool) : Frame wordWidth clockWidth :=
  ⟨first, second, 0, ⟨false, false, false, iteration⟩⟩

/-- Compose the alignment instructions; correspondence with the source is proved only until wrap. -/
def repeatPrefix : Nat → Frame wordWidth clockWidth → Frame wordWidth clockWidth
  | 0, state => state
  | count + 1, state => alignmentPrefix (repeatPrefix count state)

/-- Exact intermediate tracked coordinates before the first actual finite-counter wrap. -/
def position (count : Nat) (first second : BitVec wordWidth) (iteration : Bool) :
    Frame wordWidth clockWidth :=
  ⟨first, second.rotateLeft count, BitVec.ofNat clockWidth count,
    ⟨false, false, false, iteration⟩⟩

private lemma rotateLeft_zero (word : BitVec wordWidth) : word.rotateLeft 0 = word := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  simp only [BitVec.getMsbD_rotateLeft, Nat.zero_add, Nat.mod_eq_of_lt within,
    within, decide_true, Bool.true_and]

/-- A pre-wrap step preserves terminal phase `00` while advancing the real rotation and counter. -/
lemma step_position (count : Nat) (first second : BitVec wordWidth) (iteration : Bool)
    (beforeWrap : count + 1 < 2 ^ clockWidth) :
    alignmentPrefix (position (clockWidth := clockWidth) count first second iteration) =
      position (count + 1) first second iteration := by
  have nonzero := ofNat_nonzero (clockWidth := clockWidth) (count + 1) (by omega) beforeWrap
  simp only [alignmentPrefix, position, increment_ofNat, nonzero, decide_false,
    Bool.false_eq_true, if_false, WordRotation.rotateLeft_comp, zero_divisor_control]

/-- Every source step before wrap remains in the actual zero-divisor alignment branch. -/
lemma repeatPrefix_position (count : Nat) (first second : BitVec wordWidth) (iteration : Bool)
    (beforeWrap : count < 2 ^ clockWidth) :
    repeatPrefix count (start (clockWidth := clockWidth) first second iteration) =
      position count first second iteration := by
  revert beforeWrap
  induction count with
  | zero =>
    intro _
    simp only [repeatPrefix, start, position, rotateLeft_zero, literal_zero]
  | succ count inductionHypothesis =>
    intro beforeWrap
    rw [repeatPrefix, inductionHypothesis (by omega)]
    exact step_position count first second iteration beforeWrap

/-- Before wrap, the retained finite shift register records the entire actual padding length. -/
lemma retained_shift (count : Nat) (first second : BitVec wordWidth) (iteration : Bool)
    (beforeWrap : count < 2 ^ clockWidth) :
    (repeatPrefix count (start (clockWidth := clockWidth) first second iteration)).shift.toNat =
      count := by
  rw [repeatPrefix_position count first second iteration beforeWrap]
  change count % 2 ^ clockWidth = count
  exact Nat.mod_eq_of_lt beforeWrap

/-- Keeping the actual shift coordinate allows the full second work word to be recovered. -/
lemma retained_shift_recovers_word (count : Nat) (first second : BitVec wordWidth)
    (iteration : Bool) (beforeWrap : count < 2 ^ clockWidth) :
    let final := repeatPrefix count (start (clockWidth := clockWidth) first second iteration)
    final.secondWord.rotateRight final.shift.toNat = second := by
  dsimp only
  rw [retained_shift count first second iteration beforeWrap,
    repeatPrefix_position count first second iteration beforeWrap]
  exact WordRotation.rotateRight_rotateLeft second count

/-- At the first actual wrap, the source tests zero, exchanges both words, and enters phase `11`. -/
lemma first_wrap (first second : BitVec wordWidth) (iteration : Bool) :
    repeatPrefix (2 ^ clockWidth) (start (clockWidth := clockWidth) first second iteration) =
      ⟨second.rotateLeft (2 ^ clockWidth), first, 0, ⟨true, true, false, !iteration⟩⟩ := by
  have capacityPositive := Nat.two_pow_pos clockWidth
  have lastCount : 2 ^ clockWidth = (2 ^ clockWidth - 1) + 1 := by omega
  calc
    _ = repeatPrefix ((2 ^ clockWidth - 1) + 1)
        (start first second iteration) :=
      congrArg (fun count => repeatPrefix count
        (start (clockWidth := clockWidth) first second iteration)) lastCount
    _ = alignmentPrefix
        (position (2 ^ clockWidth - 1) first second iteration) := by
      rw [repeatPrefix, repeatPrefix_position _ _ _ _ (by omega)]
    _ = _ := by
      simp only [alignmentPrefix, position, increment_ofNat, ← lastCount, first_wrap_zero,
        decide_true, if_true, WordRotation.rotateLeft_comp, zero_divisor_control]

/-- The actual smallest-input terminal word does not remain idle during padding. -/
lemma smallest_terminal_not_idle :
    let terminal := start (clockWidth := 2) (9 : BitVec 5) (16 : BitVec 5) true
    (alignmentPrefix terminal).secondWord.toNat = 1 ∧
      (alignmentPrefix terminal).shift.toNat = 1 ∧ alignmentPrefix terminal ≠ terminal := by
  decide

/-- The stated two-bit length register wraps after four terminal steps and triggers exchange. -/
lemma smallest_terminal_wrap :
    let terminal := start (clockWidth := 2) (9 : BitVec 5) (16 : BitVec 5) true
    (repeatPrefix 4 terminal).firstWord.toNat = 8 ∧
      (repeatPrefix 4 terminal).secondWord.toNat = 9 ∧
      (repeatPrefix 4 terminal).shift.toNat = 0 ∧
      (repeatPrefix 4 terminal).flags = ⟨true, true, false, false⟩ := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.TerminalTail
