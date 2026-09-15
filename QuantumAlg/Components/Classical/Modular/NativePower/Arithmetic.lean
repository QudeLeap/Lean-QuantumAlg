/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.Multiply
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.Classical.Modular.Basic

/-!
# Exact arithmetic of the actual full-product reduction

The full product cannot overflow its combined width. For a positive modulus
fitting the result capacity, neither remainder representation nor the final
resize loses a bit. These are mathematical facts about the same three closed
instructions; they introduce no additional runtime operation.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

/-- The combined operand width stores the exact product without modular truncation. -/
theorem nativePower_fullProduct_exact {width : Nat} (left right : CShape.Word width) :
    (CShape.mulFull width width (.product left right)).toNat = left.toNat * right.toNat := by
  have fits : left.toNat * right.toNat < 2 ^ (width + width) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt left.toNat_lt right.toNat_lt
  change (left.toNat * right.toNat) % (2 ^ (width + width)) = _
  exact Nat.mod_eq_of_lt fits

/-- With a fitted positive modulus the actual three-operation value is exact modular product. -/
theorem nativePower_multiplyValue_toNat {width : Nat}
    (left right : CShape.Word width) (modulus : CShape.Word (width + 1))
    (positive : 0 < modulus.toNat) (fits : modulus.toNat ≤ 2 ^ width) :
    (multiplyValue left right modulus).toNat = left.toNat * right.toNat % modulus.toNat := by
  have productExact := nativePower_fullProduct_exact left right
  have remainderBound : left.toNat * right.toNat % modulus.toNat < modulus.toNat :=
    Nat.mod_lt _ positive
  change ((((CShape.mulFull width width (.product left right)).toNat % modulus.toNat) %
    (2 ^ (width + 1))) % (2 ^ width)) = _
  rw [productExact, Nat.mod_eq_of_lt (lt_trans remainderBound modulus.toNat_lt),
    Nat.mod_eq_of_lt (lt_of_lt_of_le remainderBound fits)]

/-- The result is a canonical representative of the actual fitted modulus. -/
theorem nativePower_multiplyValue_lt {width : Nat}
    (left right : CShape.Word width) (modulus : CShape.Word (width + 1))
    (positive : 0 < modulus.toNat) (fits : modulus.toNat ≤ 2 ^ width) :
    (multiplyValue left right modulus).toNat < modulus.toNat := by
  rw [nativePower_multiplyValue_toNat left right modulus positive fits]
  exact Nat.mod_lt _ positive

/-- The intrinsic specification's extended word carries the original modulus exactly. -/
theorem nativePower_multiplyValue_spec {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (left right : CShape.Word width) :
    (multiplyValue left right (.unsignedWord spec.extendedWord)).toNat =
      left.toNat * right.toNat % spec.modulus :=
  nativePower_multiplyValue_toNat left right (.unsignedWord spec.extendedWord)
    (ClassicalAlgorithms.Modular.modulusSpec_modulus_pos spec) spec.le_capacity

end QuantumAlg.ClassicalRoutines.Modular.NativePower
