/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Nat.FixedWidth.Modular.Word.Equiv
import all QuantumAlg.Util.ZModUnits

/-!
# Finite unit multiplication and clean auxiliary-word cancellation

The forward selected accumulation computes the product into a zero word.
After exchanging the words, accumulation with the inverse unit maps zero
back to the original input. These identities support the exact adjoint
cleanup in [G17, paper.tex:186-211]. Unit equations are used in `ZMod N`,
so modulus one is included without the incorrect natural equation `0 = 1`.
-/

namespace QuantumAlg.Nat.FixedWidth

/-- Multiply a word by the compiled unit and return its canonical residue. -/
def unitProductWord {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) : Fin (2 ^ width) :=
  ⟨((coefficient : ZMod modulus.val).val * input.val) % modulus.val,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ positive) (Nat.le_of_lt_succ modulus.isLt)⟩

theorem unitProductWord_valid {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) :
    (unitProductWord modulus positive coefficient input).val < modulus.val :=
  Nat.mod_lt _ positive

/-- Zero-seeded accumulation is precisely the independent canonical unit product. -/
theorem unitProductWord_accumulate_zero {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) :
    accumulateWordPrefix modulus (coefficient : ZMod modulus.val).val input 0 width =
      unitProductWord modulus positive coefficient input := by
  apply Fin.ext
  have h := accumulateWordPrefix_full modulus (coefficient : ZMod modulus.val).val input 0 positive
  simpa only [Fin.val_zero, Nat.zero_add, unitProductWord] using h

/-- Applying the inverse unit restores every canonical input, including modulus one. -/
theorem unitProductWord_inverse {width : Nat} (modulus : Fin (2 ^ width + 1))
    (positive : 0 < modulus.val) (coefficient : (ZMod modulus.val)ˣ)
    (input : Fin (2 ^ width)) (valid : input.val < modulus.val) :
    unitProductWord modulus positive coefficient⁻¹
      (unitProductWord modulus positive coefficient input) = input := by
  let : NeZero modulus.val := ⟨Nat.ne_of_gt positive⟩
  have cancel : ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val) *
      ((coefficient : ZMod modulus.val) * (input.val : ZMod modulus.val)) =
        (input.val : ZMod modulus.val) := by
    simp
  have values := congrArg ZMod.val cancel
  rw [ZMod.val_mul, ZMod.val_mul, ZMod.val_natCast_of_lt valid] at values
  apply Fin.ext
  exact values

/-- The inverse accumulation computes the original input from the product and a zero target. -/
theorem unitProductWord_inverse_accumulate_zero {width : Nat}
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) (input : Fin (2 ^ width))
    (valid : input.val < modulus.val) :
    accumulateWordPrefix modulus ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
        (unitProductWord modulus positive coefficient input) 0 width = input :=
  (unitProductWord_accumulate_zero modulus positive coefficient⁻¹ _).trans
    (unitProductWord_inverse modulus positive coefficient input valid)

/-- The complete reversible two-word extension of compute, swap, and inverse compute. -/
def unitMultiplicationPairEquiv {width : Nat} (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) : Equiv.Perm (Fin (2 ^ width) × Fin (2 ^ width)) :=
  (accumulatePairEquiv modulus (coefficient : ZMod modulus.val).val width).trans
    (Equiv.prodComm _ _) |>.trans
      (accumulatePairEquiv modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val width).symm

/-- A zero auxiliary word is returned exactly for every canonical input residue. -/
theorem unitMultiplicationPairEquiv_clean {width : Nat}
    (modulus : Fin (2 ^ width + 1)) (positive : 0 < modulus.val)
    (coefficient : (ZMod modulus.val)ˣ) (input : Fin (2 ^ width))
    (valid : input.val < modulus.val) :
    unitMultiplicationPairEquiv modulus coefficient (input, 0) =
      (unitProductWord modulus positive coefficient input, 0) := by
  change (accumulatePairEquiv modulus
    ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val width).symm
      ((accumulatePairEquiv modulus (coefficient : ZMod modulus.val).val width
        (input, 0)).swap) = _
  apply (accumulatePairEquiv modulus
    ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val width).injective
  rw [Equiv.apply_symm_apply, accumulatePairEquiv_apply, accumulatePairEquiv_apply]
  change (accumulateWordPrefix modulus (coefficient : ZMod modulus.val).val
      input 0 width, input) =
    (unitProductWord modulus positive coefficient input,
      accumulateWordPrefix modulus
        ((coefficient⁻¹ : (ZMod modulus.val)ˣ) : ZMod modulus.val).val
        (unitProductWord modulus positive coefficient input) 0 width)
  rw [unitProductWord_accumulate_zero,
    unitProductWord_inverse_accumulate_zero modulus positive coefficient input valid]

end QuantumAlg.Nat.FixedWidth
