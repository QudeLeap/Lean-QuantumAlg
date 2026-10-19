/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail
import all QuantumAlg.Util.NumberTheory.SharedEEA.Alignment
import all QuantumAlg.Util.NumberTheory.SharedEEA.Capacity

/-!
# Actual finite shift arithmetic at active shared-EEA boundaries

The optimized source executes a finite increment before its conditional
subtraction by two in the descending phases. The word rotations occur in
the same order [LYL+26, sec_EEA/sub_opt.tex:37-40,68-70]. The zero-counter
control test occurs after these operations [LYL+26, sec_EEA/sub_opt.tex:77-84].

This owner proves the literal counter assignments, including the genuine
intermediate modular value. Increasing the counter width by two preserves
the narrow projection even if the original intermediate increment wraps.
At each valid active control boundary, both counters encode the same
natural count and every added high bit is zero. It would be incorrect to
assert that the intermediate increment always has zero high bits.

The actual comparison-driven alignment supplies the bounded counts from
the existing reachable invariant; no quotient is used to initialize the
phase. These are finite arithmetic refinement laws, not a replacement
interpreter, a complete four-phase composition, or a gate cost theorem.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.ShiftArithmetic

variable {clockWidth : Nat}

/-- The exact ordered finite assignments in an optimized descending shift. -/
def decrementPair (shift : BitVec clockWidth) : BitVec clockWidth := (shift + 1) - 2

/-- The ordered pair decrements a positive natural count even if its intermediate value wraps. -/
lemma decrementPair_ofNat (count : Nat) (positive : 0 < count) :
    decrementPair (BitVec.ofNat clockWidth count) = BitVec.ofNat clockWidth (count - 1) := by
  change (BitVec.ofNat clockWidth count + BitVec.ofNat clockWidth 1) -
    BitVec.ofNat clockWidth 2 = BitVec.ofNat clockWidth (count - 1)
  rw [BitVec.sub_eq_iff_eq_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 1
  omega

/-- Reverse the actual subtraction first, then reverse the actual preceding increment. -/
lemma rewind_decrementPair (shift : BitVec clockWidth) :
    (decrementPair shift + 2) - 1 = shift := by
  unfold decrementPair
  rw [BitVec.sub_add_cancel, BitVec.add_sub_cancel]

/-- Projection of the true intermediate increment agrees at every finite count. -/
lemma increment_narrow (width count : Nat) :
    (BitVec.ofNat (width + 2) count + 1).setWidth width = BitVec.ofNat width count + 1 := by
  rw [TerminalTail.increment_ofNat, TerminalTail.increment_ofNat]
  exact BitVec.setWidth_ofNat_of_le (by omega) _

/-- The complete descending assignment has the same original finite-register projection. -/
lemma decrementPair_narrow (width count : Nat) (positive : 0 < count) :
    (decrementPair (BitVec.ofNat (width + 2) count)).setWidth width =
      decrementPair (BitVec.ofNat width count) := by
  rw [decrementPair_ofNat count positive, decrementPair_ofNat count positive]
  exact BitVec.setWidth_ofNat_of_le (by omega) _

private lemma encoded_zero_iff (count : Nat) (within : count < 2 ^ clockWidth) :
    BitVec.ofNat clockWidth count = 0 ↔ count = 0 := by
  constructor
  · intro zero
    have values := congrArg BitVec.toNat zero
    change count % 2 ^ clockWidth = 0 at values
    simpa only [Nat.mod_eq_of_lt within] using values
  · intro zero
    apply BitVec.eq_of_toNat_eq
    change count % 2 ^ clockWidth = 0
    rw [zero, Nat.zero_mod]

/-- Every active count fitting the original input width fits the original counter exactly. -/
lemma original_value (width count : Nat) (within : count ≤ width) :
    (BitVec.ofNat width.size count).toNat = count :=
  Nat.mod_eq_of_lt (within.trans_lt (Nat.lt_size_self width))

/-- The same active count fits the extended counter exactly. -/
lemma extended_value (width count : Nat) (within : count ≤ width) :
    (BitVec.ofNat (width.size + 2) count).toNat = count := by
  have below := within.trans_lt (Nat.lt_size_self width)
  exact Nat.mod_eq_of_lt
    (below.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))

/-- At valid active boundaries, every added high position is actually zero. -/
lemma boundary_high_zero (width count index : Nat) (within : count ≤ width)
    (high : width.size ≤ index) :
    (BitVec.ofNat (width.size + 2) count).getLsbD index = false := by
  change (BitVec.ofNat (width.size + 2) count).toNat.testBit index = false
  rw [extended_value width count within]
  exact Nat.testBit_lt_two_pow ((within.trans_lt (Nat.lt_size_self width)).trans_le
    (Nat.pow_le_pow_right Nat.zero_lt_two high))

/-- The actual full-register zero predicates agree at every active control boundary. -/
lemma boundary_zero_iff (width count : Nat) (within : count ≤ width) :
    BitVec.ofNat (width.size + 2) count = 0 ↔ BitVec.ofNat width.size count = 0 := by
  have below := within.trans_lt (Nat.lt_size_self width)
  have extendedBelow := below.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two
    (show width.size ≤ width.size + 2 by omega))
  exact (encoded_zero_iff count extendedBelow).trans (encoded_zero_iff count below).symm

/-- The real intermediate original value is modular; the extended value is the full increment. -/
lemma increment_values (width count : Nat) (within : count ≤ width) :
    (BitVec.ofNat width.size count + 1).toNat = (count + 1) % 2 ^ width.size ∧
      (BitVec.ofNat (width.size + 2) count + 1).toNat = count + 1 := by
  rw [TerminalTail.increment_ofNat, TerminalTail.increment_ofNat]
  refine ⟨rfl, ?_⟩
  have below := within.trans_lt (Nat.lt_size_self width)
  have capacity : 2 ^ width.size < 2 ^ (width.size + 2) :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by omega)
  exact Nat.mod_eq_of_lt (by omega)

/-- An ascending phase tests its actual increment only within the original active count bound. -/
lemma increment_boundary (width count : Nat) (within : count < width) :
    (BitVec.ofNat width.size count + 1).toNat = count + 1 ∧
      (BitVec.ofNat (width.size + 2) count + 1).toNat = count + 1 := by
  rw [TerminalTail.increment_ofNat, TerminalTail.increment_ofNat]
  exact ⟨original_value width (count + 1) (by omega),
    extended_value width (count + 1) (by omega)⟩

/-- Both actual descending assignments reach the same exact count at their control boundary. -/
lemma decrementPair_values (width count : Nat) (positive : 0 < count)
    (within : count ≤ width) :
    (decrementPair (BitVec.ofNat width.size count)).toNat = count - 1 ∧
      (decrementPair (BitVec.ofNat (width.size + 2) count)).toNat = count - 1 := by
  rw [decrementPair_ofNat count positive, decrementPair_ofNat count positive]
  exact ⟨original_value width (count - 1) (by omega),
    extended_value width (count - 1) (by omega)⟩

/-- Temporary increment carries have vanished from every high bit before descending control. -/
lemma decrementPair_high_zero (width count index : Nat) (positive : 0 < count)
    (within : count ≤ width) (high : width.size ≤ index) :
    (decrementPair (BitVec.ofNat (width.size + 2) count)).getLsbD index = false := by
  rw [decrementPair_ofNat count positive]
  exact boundary_high_zero width (count - 1) index (by omega) high

/-- The real post-decrement zero test selects exactly the last descending shift. -/
lemma decrementPair_zero_iff (count : Nat) (positive : 0 < count)
    (within : count < 2 ^ clockWidth) :
    decrementPair (BitVec.ofNat clockWidth count) = 0 ↔ count = 1 := by
  rw [decrementPair_ofNat count positive, encoded_zero_iff (count - 1) (by omega)]
  omega

/-- Actual first-phase alignment stays within the conserved modulus width on reachable states. -/
lemma alignment_places_bound (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (Alignment.align state.remainder state.divisor).places ≤ modulus.size :=
  (Alignment.align_places_le state.remainder state.divisor).trans
    (Nat.size_le_size (Capacity.iteration_fields_le state modulus valid conserved).1)

/-- Reachable alignment and its phase prefixes establish exact counters without a caller bound. -/
lemma alignment_counter_values (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (BitVec.ofNat modulus.size.size count).toNat = count ∧
      (BitVec.ofNat (modulus.size.size + 2) count).toNat = count := by
  have bound := within.trans (alignment_places_bound state modulus valid conserved)
  exact ⟨original_value modulus.size count bound, extended_value modulus.size count bound⟩

/-- A genuine possible intermediate carry is retained, then removed by the actual subtraction. -/
lemma intermediate_wrap_boundary :
    (BitVec.ofNat 2 3 + 1).toNat = 0 ∧
      (BitVec.ofNat 4 3 + 1).toNat = 4 ∧
      (decrementPair (BitVec.ofNat 2 3)).toNat = 2 ∧
      (decrementPair (BitVec.ofNat 4 3)).toNat = 2 := by
  decide

end QuantumAlg.NumberTheory.SharedEEA.ShiftArithmetic
