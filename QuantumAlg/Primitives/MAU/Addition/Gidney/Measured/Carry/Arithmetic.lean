/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Arithmetic

/-!
# Cancellation of arbitrary dirty values in the two carry sweeps

These Boolean recurrences state the row invariant used by the actual native
carry word. They keep every original dirty value arbitrary. Native gate-fold
semantics must establish that the descending and ascending lists implement
these recurrences [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Carry

/-- Outgoing carries of arbitrary input and offset bit streams, with zero incoming carry. -/
def carry (input offset : Nat → Bool) : Nat → Bool
  | 0 => false
  | index + 1 => Bool.carry (input index) (offset index) (carry input offset index)

/-- The ascending value after the descending dirty contribution and offset xor. -/
def ascendingValue (input offset dirty : Nat → Bool) : Nat → Bool
  | 0 => (dirty 0 ^^ offset 0) ^^ ((input 0 ^^ offset 0) && offset 0)
  | index + 1 =>
      (((dirty (index + 1) ^^ ((input (index + 1) ^^ offset (index + 1)) && dirty index)) ^^
        offset (index + 1)) ^^
          ((input (index + 1) ^^ offset (index + 1)) &&
            (ascendingValue input offset dirty index ^^ offset (index + 1))))

/-- Every arbitrary original dirty bit survives, xored with exactly its outgoing carry. -/
lemma ascendingValue_eq_dirty_xor_carry (input offset dirty : Nat → Bool) (index : Nat) :
    ascendingValue input offset dirty index = (dirty index ^^ carry input offset (index + 1)) := by
  induction index with
  | zero =>
      change ((dirty 0 ^^ offset 0) ^^ ((input 0 ^^ offset 0) && offset 0)) =
        (dirty 0 ^^ Bool.carry (input 0) (offset 0) false)
      rw [first_carry_xor]
      cases input 0 <;> cases offset 0 <;> cases dirty 0 <;> rfl
  | succ index ih =>
      change ascendingValue input offset dirty (index + 1) =
        (dirty (index + 1) ^^
          Bool.carry (input (index + 1)) (offset (index + 1))
            (carry input offset (index + 1)))
      rw [ascendingValue, ih]
      exact dirty_carry_xor (input (index + 1)) (offset (index + 1))
        (carry input offset (index + 1)) (dirty index) (dirty (index + 1))

/-- Natural-word carry arithmetic is the same bit-stream recurrence. -/
lemma carry_testBit (input offset index : Nat) :
    carry input.testBit offset.testBit index =
      Nat.BinaryArithmetic.natAddCarry input offset index := by
  induction index with
  | zero => rfl
  | succ index ih => rw [carry, Nat.BinaryArithmetic.natAddCarry, ih]

end QuantumAlg.MAU.Addition.Gidney.Measured.Carry
