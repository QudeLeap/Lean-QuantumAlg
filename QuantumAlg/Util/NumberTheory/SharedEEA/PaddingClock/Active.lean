/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PaddingClock
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.PackedStep

/-!
# Active counter updates retain arbitrary existing high-position data

The enlarged physical clock includes two original Work1 bits which need
not be zero during active computation. A low increment below its original
capacity, or a decrement from a positive low value, retains those bits
exactly. The actual descending sequence first increments and then performs
two decrements [LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. Its first inverse
decrement restores the entire intermediate carry, even if that carry
wrapped through arbitrary incoming high data.

These are exact finite-word equations for the already proved physical
clock split and join. Reachable phase counts must supply the local low
bounds at integration; no high-bit zero promise is assumed. The equations
neither omit any actual increment/decrement gate nor make terminal
padding idle.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.PaddingClockActive

variable {highWidth lowWidth mainWidth : Nat}

private theorem append_increment (high : BitVec highWidth) (low : BitVec lowWidth)
    (within : low.toNat + 1 < 2 ^ lowWidth) :
    (high ++ low) + 1 = high ++ (low + 1) := by
  have upper := Nat.mul_le_mul_right (2 ^ lowWidth)
    (show high.toNat + 1 ≤ 2 ^ highWidth from high.isLt)
  rw [Nat.add_mul, Nat.one_mul] at upper
  have fullWithin : high.toNat * 2 ^ lowWidth + low.toNat + 1 <
      2 ^ (highWidth + lowWidth) := by
    rw [Nat.pow_add]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [TerminalTail.increment_toNat, DivisionPackedStep.append_toNat,
    DivisionPackedStep.append_toNat, TerminalTail.increment_toNat,
    Nat.mod_eq_of_lt within, Nat.mod_eq_of_lt fullWithin]
  omega

private theorem append_decrement (high : BitVec highWidth) (low : BitVec lowWidth)
    (positive : 0 < low.toNat) :
    (high ++ low) - 1 = high ++ (low - 1) := by
  have capacity := low.isLt
  have one : (1 : BitVec lowWidth).toNat = 1 := by
    change (1 : Nat) % 2 ^ lowWidth = 1
    exact Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ lowWidth by omega)
  have below : (1 : BitVec lowWidth) ≤ low := by
    rw [BitVec.le_def, one]
    exact positive
  have smaller := BitVec.toNat_sub_of_le below
  rw [one] at smaller
  have within : (low - 1).toNat + 1 < 2 ^ lowWidth := by
    rw [smaller]
    omega
  have restored := append_increment high (low - 1) within
  rw [BitVec.sub_add_cancel] at restored
  exact BitVec.sub_eq_iff_eq_add.mpr restored.symm

/-- A real active ascending step leaves every original Work1 bit unchanged. -/
theorem increment_eq_low (state : BitVec (mainWidth + 3) × BitVec lowWidth)
    (within : state.2.toNat + 1 < 2 ^ lowWidth) :
    PaddingClock.increment state = (state.1, state.2 + 1) := by
  unfold PaddingClock.increment
  change PaddingClock.join
    ((PaddingClock.main state.1, PaddingClock.last state.1),
      (PaddingClock.high state.1 ++ state.2) + 1) = _
  rw [append_increment _ _ within]
  exact PaddingClock.join_split (state.1, state.2 + 1)

/-- A real active decrement preserves arbitrary high-position data, not only zero padding. -/
theorem decrement_eq_low (state : BitVec (mainWidth + 3) × BitVec lowWidth)
    (positive : 0 < state.2.toNat) :
    PaddingClock.decrement state = (state.1, state.2 - 1) := by
  unfold PaddingClock.decrement
  change PaddingClock.join
    ((PaddingClock.main state.1, PaddingClock.last state.1),
      (PaddingClock.high state.1 ++ state.2) - 1) = _
  rw [append_decrement _ _ positive]
  exact PaddingClock.join_split (state.1, state.2 - 1)

/-- Both inverse increments follow the real increment; arbitrary intermediate carry is undone. -/
theorem descending_eq_low (state : BitVec (mainWidth + 3) × BitVec lowWidth)
    (positive : 0 < state.2.toNat) :
    PaddingClock.decrement (PaddingClock.decrement (PaddingClock.increment state)) =
      (state.1, state.2 - 1) := by
  rw [PaddingClock.decrement_increment]
  exact decrement_eq_low state positive

/-- An ascending reachable count below the input width supplies the original low capacity itself. -/
theorem active_increment (width count : Nat) (word : BitVec (width + 3))
    (within : count < width) :
    PaddingClock.increment (word, BitVec.ofNat width.size count) =
      (word, BitVec.ofNat width.size count + 1) := by
  apply increment_eq_low
  have exactCount : (BitVec.ofNat width.size count).toNat = count :=
    Nat.mod_eq_of_lt (within.trans (Nat.lt_size_self width))
  rw [exactCount]
  exact (show count + 1 ≤ width from within).trans_lt (Nat.lt_size_self width)

/-- Each positive reachable descending count supplies the required no-borrow boundary internally. -/
theorem active_descending (width count : Nat) (word : BitVec (width + 3))
    (positive : 0 < count) (within : count ≤ width) :
    PaddingClock.decrement (PaddingClock.decrement
      (PaddingClock.increment (word, BitVec.ofNat width.size count))) =
        (word, BitVec.ofNat width.size count - 1) := by
  apply descending_eq_low
  have exactCount : (BitVec.ofNat width.size count).toNat = count :=
    Nat.mod_eq_of_lt (within.trans_lt (Nat.lt_size_self width))
  simpa only [exactCount] using positive

end QuantumAlg.NumberTheory.SharedEEA.PaddingClockActive
