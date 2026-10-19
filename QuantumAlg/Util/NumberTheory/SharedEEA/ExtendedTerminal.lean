/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Quotient.Schedule
import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail

/-!
# Exact scheduled terminal trajectory with two additional counter bits

The terminal branch still executes the source's actual circular left
rotation and finite increment. Its subsequent zero-counter test controls
the real word exchange and flag update
[LYL+26, sec_EEA/sub_opt.tex:37-48,74-84]. This owner uses precisely the
existing `TerminalTail.alignmentPrefix`; it introduces no idle branch.

The independently proved quotient schedule bounds the terminal padding.
With `Nat.size n + 2` counter bits, every scheduled prefix is before wrap.
The entire tracked state is determined: the first word and flags persist,
the second word rotates, and the retained counter records that rotation.
Right rotation by the actual retained counter recovers the entire second
word. Reversing the actual prefix assignments also recovers every tracked
coordinate, including the counter; forward decoding does not erase it.

The extra counter bits and final inverse rotation are an internal repair
candidate, not instructions claimed to occur in the registered source.
Agreement with the source's active phases at the wider counter width,
placement of those two bits, literal quantum gates, and gate accounting
are separate obligations. The source's retained forward state is explicit
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128].
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ExtendedTerminal

variable {wordWidth clockWidth : Nat}

/-- Reverse the very same finite assignments in their opposite temporal order. -/
def rewind : Nat → TerminalTail.Frame wordWidth clockWidth →
    TerminalTail.Frame wordWidth clockWidth
  | 0, state => state
  | count + 1, state => rewind count (TerminalTail.rewindPrefix state)

/-- Literal reverse execution restores all tracked data for any finite prefix. -/
lemma rewind_repeatPrefix (count : Nat) (state : TerminalTail.Frame wordWidth clockWidth) :
    rewind count (TerminalTail.repeatPrefix count state) = state := by
  induction count generalizing state with
  | zero => rfl
  | succ count inductionHypothesis =>
    change rewind count (TerminalTail.rewindPrefix
      (TerminalTail.alignmentPrefix (TerminalTail.repeatPrefix count state))) = state
    rw [TerminalTail.rewind_alignmentPrefix]
    exact inductionHypothesis state

/-- Every scheduled prefix has its complete rotating state, with no finite-counter wrap. -/
lemma prefix_position (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) (count : Nat)
    (within : count ≤ QuotientSchedule.padding modulus input)
    (first second : BitVec wordWidth) (iteration : Bool) :
    TerminalTail.repeatPrefix count
        (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration) =
      TerminalTail.position count first second iteration :=
  TerminalTail.repeatPrefix_position count first second iteration
    (within.trans_lt
      (QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded))

/-- Each scheduled next increment is actually nonzero, so it cannot select exchange or refresh. -/
lemma next_shift_nonzero (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus) (count : Nat)
    (within : count < QuotientSchedule.padding modulus input)
    (first second : BitVec wordWidth) (iteration : Bool) :
    (TerminalTail.repeatPrefix count
      (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration)).shift + 1
        ≠ 0 := by
  have below := QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded
  have nextBelow : count + 1 < 2 ^ (modulus.size.size + 2) := by omega
  rw [prefix_position modulus input coprime positive bounded count within.le first second iteration]
  change BitVec.ofNat (modulus.size.size + 2) count + 1 ≠ 0
  rw [TerminalTail.increment_ofNat]
  intro zero
  have values := congrArg BitVec.toNat zero
  change (count + 1) % 2 ^ (modulus.size.size + 2) = 0 at values
  rw [Nat.mod_eq_of_lt nextBelow] at values
  omega

/-- The end of the independent schedule retains the exact words, shift, phase, sign, and parity. -/
lemma scheduled_position (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    TerminalTail.repeatPrefix (QuotientSchedule.padding modulus input)
        (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration) =
      ⟨first, second.rotateLeft (QuotientSchedule.padding modulus input),
        BitVec.ofNat (modulus.size.size + 2) (QuotientSchedule.padding modulus input),
        ⟨false, false, false, iteration⟩⟩ :=
  prefix_position modulus input coprime positive bounded _ (Nat.le_refl _) first second iteration

/-- The retained finite register contains the complete padding count, rather than its residue. -/
lemma scheduled_clock (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    (TerminalTail.repeatPrefix (QuotientSchedule.padding modulus input)
      (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration)).shift.toNat
        = QuotientSchedule.padding modulus input :=
  TerminalTail.retained_shift _ first second iteration
    (QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded)

/-- Actual right rotation controlled by the retained count recovers every bit of the second word. -/
lemma scheduled_decode (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    let final := TerminalTail.repeatPrefix (QuotientSchedule.padding modulus input)
      (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration)
    final.secondWord.rotateRight final.shift.toNat = second :=
  TerminalTail.retained_shift_recovers_word _ first second iteration
    (QuotientSchedule.padding_fits_extended_clock modulus input coprime positive bounded)

/-- The recorded count also determines the exact inverse prefix restoring every tracked register. -/
lemma rewind_scheduled (modulus input : Nat) (coprime : Nat.Coprime input modulus)
    (positive : 0 < input) (bounded : input < modulus)
    (first second : BitVec wordWidth) (iteration : Bool) :
    let final := TerminalTail.repeatPrefix (QuotientSchedule.padding modulus input)
      (TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration)
    rewind final.shift.toNat final =
      TerminalTail.start (clockWidth := modulus.size.size + 2) first second iteration := by
  dsimp only
  rw [scheduled_clock modulus input coprime positive bounded first second iteration]
  exact rewind_repeatPrefix _ _

/-- The smallest terminal word still rotates; its widened counter prevents the former swap. -/
lemma smallest_extended_four_steps :
    let terminal := TerminalTail.start (clockWidth := 4) (9 : BitVec 5) (16 : BitVec 5) true
    let final := TerminalTail.repeatPrefix 4 terminal
    final.firstWord.toNat = 9 ∧ final.secondWord.toNat = 8 ∧ final.shift.toNat = 4 ∧
      final.flags = ⟨false, false, false, true⟩ ∧
      (final.secondWord.rotateRight final.shift.toNat).toNat = 16 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.ExtendedTerminal
