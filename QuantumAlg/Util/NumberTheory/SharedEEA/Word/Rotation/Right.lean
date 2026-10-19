/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Terminal.Tail
import Mathlib.Data.Fintype.EquivFin

/-!
# Composition of the exact finite-word inverse rotations

The source retains the full forward rotation history for inverse
computation [LYL+26, sec_EEA/sub_4phase.tex:105,121-128]. The already
proved complete-word left/right inverse gives both inverse directions
on the finite word space and additive composition of right rotations.
Empty words and arbitrary retained rotation counts are included.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.WordRotationRight

variable {width : Nat}

private lemma left_injective (width count : Nat) :
    Function.Injective (fun word : BitVec width => word.rotateLeft count) :=
  (show Function.LeftInverse (fun word : BitVec width => word.rotateRight count)
    (fun word => word.rotateLeft count) from
      fun word => WordRotation.rotateRight_rotateLeft word count).injective

/-- The opposite composition also restores the complete finite word. -/
lemma rotateLeft_rotateRight (word : BitVec width) (count : Nat) :
    (word.rotateRight count).rotateLeft count = word := by
  let toFin : BitVec width → Fin (2 ^ width) := fun value => ⟨value.toNat, value.isLt⟩
  let : Finite (BitVec width) := Finite.of_injective toFin (by
    intro left right same
    apply BitVec.eq_of_toNat_eq
    exact congrArg (fun value : Fin (2 ^ width) => value.val) same)
  obtain ⟨original, rfl⟩ := (Finite.surjective_of_injective (left_injective width count)) word
  rw [WordRotation.rotateRight_rotateLeft]

/-- Successive actual right rotations add their full retained displacements. -/
lemma rotateRight_comp (word : BitVec width) (first second : Nat) :
    (word.rotateRight first).rotateRight second = word.rotateRight (first + second) := by
  apply left_injective width (first + second)
  change ((word.rotateRight first).rotateRight second).rotateLeft (first + second) =
    (word.rotateRight (first + second)).rotateLeft (first + second)
  conv_lhs => rw [Nat.add_comm first second, ← WordRotation.rotateLeft_comp]
  rw [rotateLeft_rotateRight, rotateLeft_rotateRight, rotateLeft_rotateRight]

/-- A zero inverse displacement preserves every bit, including an empty word. -/
lemma rotateRight_zero (word : BitVec width) : word.rotateRight 0 = word := by
  simpa only [TerminalTail.rotateLeft_zero] using WordRotation.rotateRight_rotateLeft word 0

end QuantumAlg.NumberTheory.SharedEEA.WordRotationRight
