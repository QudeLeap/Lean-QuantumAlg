/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Canonical cancellation by explicitly added negative inverse-unit residues

The arithmetic identity concerns additions of negative residues, rather
than the adjoint of a measured operation. The unit equation is established
in `ZMod N`, so the degenerate positive modulus one remains included
[VBE95, 9511018.tex:333-367; G25, main.tex:199-295].
-/

namespace QuantumAlg.Nat.FixedWidth

/-- An explicit negative-inverse product addition clears the original canonical input. -/
lemma negativeUnitProduct_add_cancel (modulus : Nat) (positive : 0 < modulus)
    (coefficient : (ZMod modulus)ˣ) (input : Nat) :
    (input + (modulus - ((coefficient⁻¹ : (ZMod modulus)ˣ) : ZMod modulus).val % modulus) *
      (((coefficient : ZMod modulus).val * input) % modulus)) % modulus = 0 := by
  let : NeZero modulus := ⟨Nat.ne_of_gt positive⟩
  have castSum :
      ((input +
        (modulus - ((coefficient⁻¹ : (ZMod modulus)ˣ) : ZMod modulus).val % modulus) *
          (((coefficient : ZMod modulus).val * input) % modulus) : Nat) : ZMod modulus) = 0 := by
    rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ positive))]
    simp only [ZMod.natCast_self, zero_sub, ZMod.natCast_mod, Nat.cast_mul,
      ZMod.natCast_zmod_val]
    simp [← mul_assoc]
  have residues := (ZMod.natCast_eq_natCast_iff'
    (input + (modulus - ((coefficient⁻¹ : (ZMod modulus)ˣ) : ZMod modulus).val % modulus) *
      (((coefficient : ZMod modulus).val * input) % modulus)) 0 modulus).mp
        (castSum.trans (Nat.cast_zero).symm)
  simpa only [Nat.zero_mod] using residues

end QuantumAlg.Nat.FixedWidth
