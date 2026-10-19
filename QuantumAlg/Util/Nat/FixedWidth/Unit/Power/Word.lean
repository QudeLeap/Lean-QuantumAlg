/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Unit.Word.Multiplication

/-!
# Canonical binary representatives of modular units

Compiled units determine canonical finite words. Their products agree with
the independently specified word multiplier. The identity unit is encoded
by one modulo the modulus, so modulus one and width zero require no missing
or noncanonical initial label [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.Nat.FixedWidth

/-- Canonical finite-word representative of a modular unit. -/
def unitResidueWord {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (unit : (ZMod modulus.val)ˣ) : Fin (2 ^ width) :=
  ⟨(unit : ZMod modulus.val).val, by
    let : NeZero modulus.val := ⟨Nat.ne_of_gt positive⟩
    exact Nat.lt_of_lt_of_le (ZMod.val_lt (unit : ZMod modulus.val))
      (Nat.le_of_lt_succ modulus.isLt)⟩

lemma unitResidueWord_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (unit : (ZMod modulus.val)ˣ) :
    (unitResidueWord modulus positive unit).val < modulus.val := by
  let : NeZero modulus.val := ⟨Nat.ne_of_gt positive⟩
  exact ZMod.val_lt (unit : ZMod modulus.val)

/-- The compiled initial power is one modulo the modulus, including modulus one. -/
lemma unitResidueWord_one_val {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) :
    (unitResidueWord modulus positive 1).val = 1 % modulus.val :=
  ZMod.val_one_eq_one_mod modulus.val

/-- Word multiplication agrees with multiplication of units and their canonical representatives. -/
lemma unitProductWord_unitResidueWord {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (left right : (ZMod modulus.val)ˣ) :
    unitProductWord modulus positive left (unitResidueWord modulus positive right) =
      unitResidueWord modulus positive (left * right) := by
  apply Fin.ext
  exact (ZMod.val_mul (left : ZMod modulus.val) (right : ZMod modulus.val)).symm

end QuantumAlg.Nat.FixedWidth
