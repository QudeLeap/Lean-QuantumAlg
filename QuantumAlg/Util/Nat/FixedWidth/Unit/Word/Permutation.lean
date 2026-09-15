/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication

/-!
# A single-word permutation extending canonical unit multiplication

On canonical residues the action is the independently specified unit
product; all binary padding labels are fixed. Multiplication by the
inverse unit is the exact inverse on the entire finite word. This is a
mathematical total extension for the in-place arithmetic interfaces
[LYL+26, sec_point_add/sec_point_add.tex:24-36]. It assigns no behavior to
an implementation outside its original promised input domain.
-/

namespace QuantumAlg.Nat.FixedWidth

/-- Unit multiplication on canonical residues, with identity on every padding label. -/
def unitProductWordPerm {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ) :
    Equiv.Perm (Fin (2 ^ width)) where
  toFun input := if input.val < modulus.val then
    unitProductWord modulus positive coefficient input else input
  invFun input := if input.val < modulus.val then
    unitProductWord modulus positive coefficient⁻¹ input else input
  left_inv input := by
    dsimp only
    by_cases valid : input.val < modulus.val
    · rw [if_pos valid, if_pos (unitProductWord_valid modulus positive coefficient input)]
      exact unitProductWord_inverse modulus positive coefficient input valid
    · rw [if_neg valid, if_neg valid]
  right_inv input := by
    dsimp only
    by_cases valid : input.val < modulus.val
    · rw [if_pos valid, if_pos (unitProductWord_valid modulus positive coefficient⁻¹ input)]
      simpa only [inv_inv] using
        unitProductWord_inverse modulus positive coefficient⁻¹ input valid
    · rw [if_neg valid, if_neg valid]

/-- Canonical labels follow exactly the independent modular product. -/
theorem unitProductWordPerm_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (valid : input.val < modulus.val) :
    unitProductWordPerm modulus positive coefficient input =
      unitProductWord modulus positive coefficient input :=
  if_pos valid

/-- The complete binary padding region is fixed, without discarding any finite label. -/
theorem unitProductWordPerm_padding {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (padding : ¬input.val < modulus.val) :
    unitProductWordPerm modulus positive coefficient input = input :=
  if_neg padding

/-- The actual inverse equivalence is multiplication by the inverse unit on the same domain. -/
theorem unitProductWordPerm_symm {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ) :
    (unitProductWordPerm modulus positive coefficient).symm =
      unitProductWordPerm modulus positive coefficient⁻¹ := by
  apply Equiv.ext
  intro input
  rfl

/-- The identity unit fixes all labels, including modulus one and width zero. -/
theorem unitProductWordPerm_one {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) :
    unitProductWordPerm modulus positive 1 = Equiv.refl (Fin (2 ^ width)) := by
  apply Equiv.ext
  intro input
  by_cases valid : input.val < modulus.val
  · rw [unitProductWordPerm_valid modulus positive 1 input valid]
    apply Fin.ext
    have values := congrArg ZMod.val
      (one_mul (input.val : ZMod modulus.val))
    rw [ZMod.val_mul, ZMod.val_natCast_of_lt valid] at values
    exact values
  · exact unitProductWordPerm_padding modulus positive 1 input valid

end QuantumAlg.Nat.FixedWidth
