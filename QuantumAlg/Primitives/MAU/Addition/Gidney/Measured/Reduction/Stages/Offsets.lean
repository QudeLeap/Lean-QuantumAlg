/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Data.BitVec

/-!
# Exact finite-word offsets of the literal measured reduction

Canonical positive-modulus inputs determine the same natural offsets used
by the independent two-addition arithmetic. Both actual finite-word additions
retain their exact modulo-capacity meaning [G25, main.tex:199-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction

variable {width : Nat}

/-- The actual finite-word addition selected by a Boolean flag has its exact natural readout. -/
lemma selected_add_nat (input offset : BitVec width) (selected : Bool) :
    (input + if selected then offset else 0).toNat =
      if selected then (input.toNat + offset.toNat) % 2 ^ width else input.toNat := by
  cases selected with
  | false =>
      change (input + 0).toNat = input.toNat
      rw [add_zero]
  | true =>
      exact BitVec.toNat_add input offset

/-- The actual first threshold is exactly the natural difference of canonical modulus and offset. -/
lemma firstThreshold_nat (modulus constant : BitVec width)
    (constantBound : constant.toNat < modulus.toNat) :
    (modulus - constant).toNat = modulus.toNat - constant.toNat := by
  apply BitVec.toNat_sub_of_le
  rw [BitVec.le_def]
  omega

/-- The actual second finite-word offset is the exact capacity complement used in reduction. -/
lemma secondOffset_nat (modulus constant : BitVec width)
    (constantBound : constant.toNat < modulus.toNat) :
    (constant - modulus).toNat = 2 ^ width + constant.toNat - modulus.toNat := by
  rw [BitVec.toNat_sub_of_lt (by exact constantBound)]
  have modulusFits := modulus.isLt
  omega

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction
