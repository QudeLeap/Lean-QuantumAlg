/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Finite binary labels under a permutation of their wires

The label equivalence moves a coordinate from wire `i` to wire `permutation i`.
Its readout law fixes the direction explicitly. Extending the same permutation
by identity outside its finite range gives an injective natural-number map
for physical placement, without introducing additional coordinates.
-/

namespace QuantumAlg.BinaryBasis

/-- Move each finite coordinate to its permuted position. -/
def permuteCoordinates {width : Nat} (permutation : Equiv.Perm (Fin width)) :
    (Fin width → Fin 2) ≃ (Fin width → Fin 2) where
  toFun input := fun wire => input (permutation.symm wire)
  invFun input := fun wire => input (permutation wire)
  left_inv input := by
    funext wire
    simp only [Equiv.symm_apply_apply]
  right_inv input := by
    funext wire
    simp only [Equiv.apply_symm_apply]

/-- The induced label equivalence uses the existing big-endian coordinate encoding. -/
def permuteLabel {width : Nat} (permutation : Equiv.Perm (Fin width)) :
    Equiv.Perm (Fin (2 ^ width)) :=
  (bigEndianEquiv width).symm |>.trans (permuteCoordinates permutation) |>.trans
    (bigEndianEquiv width)

/-- A bit is transported to exactly the same wire selected by the finite permutation. -/
theorem binaryPermuteLabel_bit {width : Nat} (permutation : Equiv.Perm (Fin width))
    (input : Fin (2 ^ width)) (wire : Fin width) :
    (permuteLabel permutation input).val.testBit (permutation wire).rev.val =
      input.val.testBit wire.rev.val := by
  change (bigEndianEquiv width (fun index =>
    (bigEndianEquiv width).symm input (permutation.symm index))).val.testBit
      (permutation wire).rev.val = _
  rw [bigEndianEquiv_bit]
  simp only [Equiv.symm_apply_apply, bigEndianEquiv_symm_value, Equiv.apply_symm_apply]

/-- Extend a finite wire permutation by identity on all remaining physical identifiers. -/
def extendWirePermutation {width : Nat} (permutation : Equiv.Perm (Fin width))
    (wire : Nat) : Nat :=
  if inside : wire < width then (permutation ⟨wire, inside⟩).val else wire

theorem binaryExtendWirePermutation_apply {width : Nat}
    (permutation : Equiv.Perm (Fin width)) (wire : Fin width) :
    extendWirePermutation permutation wire.val = (permutation wire).val := by
  simp only [extendWirePermutation, dif_pos wire.isLt]

theorem binaryExtendWirePermutation_outside {width : Nat}
    (permutation : Equiv.Perm (Fin width)) (wire : Nat) (outside : width ≤ wire) :
    extendWirePermutation permutation wire = wire := by
  exact dif_neg (by omega)

theorem binaryExtendWirePermutation_inverse {width : Nat}
    (permutation : Equiv.Perm (Fin width)) (wire : Nat) :
    extendWirePermutation permutation.symm (extendWirePermutation permutation wire) = wire := by
  by_cases inside : wire < width
  · let index : Fin width := ⟨wire, inside⟩
    change extendWirePermutation permutation.symm
      (extendWirePermutation permutation index.val) = index.val
    rw [binaryExtendWirePermutation_apply, binaryExtendWirePermutation_apply,
      Equiv.symm_apply_apply]
  · rw [binaryExtendWirePermutation_outside permutation wire (by omega),
      binaryExtendWirePermutation_outside permutation.symm wire (by omega)]

theorem binaryExtendWirePermutation_injective {width : Nat}
    (permutation : Equiv.Perm (Fin width)) :
    Function.Injective (extendWirePermutation permutation) := by
  intro first second equality
  have h := congrArg (extendWirePermutation permutation.symm) equality
  simpa only [binaryExtendWirePermutation_inverse] using h

theorem binaryExtendWirePermutation_range {width : Nat}
    (permutation : Equiv.Perm (Fin width)) (wire : Nat) (inside : wire < width) :
    extendWirePermutation permutation wire < width := by
  rw [extendWirePermutation, dif_pos inside]
  exact (permutation ⟨wire, inside⟩).isLt

end QuantumAlg.BinaryBasis
