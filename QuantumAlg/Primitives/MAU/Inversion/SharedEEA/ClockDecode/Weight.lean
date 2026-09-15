/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Bit
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ExtendedClock.Registers
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# Exact binary weights of the actual retained clock wires

The two reused original Work1 positions precede the original low shift
field in the complete clock. Their actual native controls therefore have
most-significant-first binary weights. Summing those weights over the
actual selecting wire values gives exactly the retained displacement,
including both high bits [LYL+26, sec_EEA/sub_4phase.tex:105,121-128].

The natural reconstruction uses the existing finite-bit sum theorem.
These coordinate laws support the actual controlled inverse-rotation
lists; they do not replace those lists by a scalar rotation callback.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeWeight

noncomputable section

open NumberTheory.SharedEEA EncodedBit PredicateLayout

/-- The actual physical clock control reads the corresponding complete finite-word digit. -/
theorem control_clock (width : Nat) (index : Fin (width.size + 2)) (state : Registers width) :
    (clockBit width index).get state =
      (ExtendedClockRegisters.clock state).getMsbD index.val := by
  let position : Fin (ExtendedClockRegisters.clockWidth width) := ⟨index.val, by
    have bound := index.isLt
    unfold ExtendedClockRegisters.clockWidth
    omega⟩
  have actual := ExtendedClockRegisters.clock_bit width position state
  change (ExtendedClockRegisters.clock state).getMsbD index.val =
    if index.val < 2 then state.firstWord.getMsbD (width + index.val)
    else state.shift.getMsbD (index.val - 2) at actual
  rw [ClockDecodeBit.control_get, actual]
  by_cases high : index.val < 2
  · rw [if_pos high, if_pos high, PaddingClock.high_bit state.firstWord index.val high]
  · rw [if_neg high, if_neg high]

/-- Each actual wire equals the correct natural test bit, with no width-only identification. -/
theorem control_testBit (width : Nat) (index : Fin (width.size + 2)) (state : Registers width) :
    (clockBit width index).get state =
      (ExtendedClockRegisters.clock state).toNat.testBit index.rev.val := by
  have within : index.val < ExtendedClockRegisters.clockWidth width := by
    have bound := index.isLt
    unfold ExtendedClockRegisters.clockWidth
    omega
  rw [control_clock, BitVec.getMsbD_eq_getLsbD, decide_eq_true within, Bool.true_and]
  change (ExtendedClockRegisters.clock state).toNat.testBit
    (2 + width.size - 1 - index.val) = _
  congr 1
  change 2 + width.size - 1 - index.val = width.size + 2 - (index.val + 1)
  omega

/-- The literal number of repeated single-rotation sweeps controlled by this actual bit. -/
def weight (width : Nat) (index : Fin (width.size + 2)) : Nat := 2 ^ index.rev.val

/-- Sum of actual selected native rotation counts over the real full-clock coordinates. -/
theorem selected_sum (width : Nat) (state : Registers width) :
    (∑ index : Fin (width.size + 2),
      ((clockBit width index).get state).toNat * weight width index) =
        (ExtendedClockRegisters.clock state).toNat := by
  let value := ExtendedClockRegisters.clock state
  have within : value.toNat < 2 ^ (width.size + 2) := by
    simpa only [ExtendedClockRegisters.clockWidth, Nat.add_comm] using value.isLt
  calc
    _ = ∑ index : Fin (width.size + 2),
        (value.toNat.testBit index.rev.val).toNat * 2 ^ index.rev.val := by
      apply Finset.sum_congr rfl
      intro index _
      rw [control_testBit]
      rfl
    _ = ∑ index : Fin (width.size + 2),
        (value.toNat.testBit index.val).toNat * 2 ^ index.val :=
      Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (width.size + 2)))
        (fun index : Fin (width.size + 2) => (value.toNat.testBit index.val).toNat * 2 ^ index.val)
    _ = Nat.ofBits (fun index : Fin (width.size + 2) => value.toNat.testBit index.val) :=
      (ExceptionalOffsetAveraging.natOfBits_eq_weightedSum _).symm
    _ = value.toNat := by
      rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt within]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeWeight
