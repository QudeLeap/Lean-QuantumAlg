/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Correction
import all QuantumAlg.Util.ResidueEncoding
import Mathlib.Algebra.Field.ZMod

/-!
# Exact source values recomputed by measured multiplication and division

The existing binary residue encoding connects the actual three-word
product's arithmetic action to the original field formulas. Multiplication
recomputes its erased input using the inverse denominator; division
recomputes it using the denominator. Only that denominator must be nonzero.
The numerator and resulting slope may be zero
[LYL+26, sec_point_add/sec_point_add.tex:67-105].

The inverse operand in these internal equations must be produced by the
actual shared EEA before composition. These equations neither emit an
inverse oracle nor remove its live history or its gate costs.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductCorrection

noncomputable section

open MAU.Multiplication Nat.FixedWidth

variable {modulus width : Nat}

/-- The original residue encoding supplies the compile-time modulus of the actual product. -/
def encodedModulus (encoding : BinaryResidueEncoding modulus width) : Fin (2 ^ width + 1) :=
  ⟨modulus, Nat.lt_succ_of_le encoding.register_fits⟩

/-- The actual independent bit-pair recurrence produces the encoded field product from zero. -/
theorem encoded_product (encoding : BinaryResidueEncoding modulus width)
    (left right : ZMod modulus) :
    variableWordPrefix (encodedModulus encoding) (encoding.encode left)
      (encoding.encode right) 0 width = encoding.encode (left * right) := by
  apply Fin.ext
  rw [variableWordPrefix_full _ _ _ _ encoding.modulus_pos]
  change (0 + left.val * right.val) % modulus = (left * right).val
  rw [Nat.zero_add, ZMod.val_mul]

/-- The native product recomputes any erased numerator of multiplication, including zero. -/
theorem encoded_multiplication_recompute [Fact modulus.Prime]
    (encoding : BinaryResidueEncoding modulus width)
    (denominator numerator : ZMod modulus) (nonzero : denominator ≠ 0) :
    variableWordPrefix (encodedModulus encoding) (encoding.encode denominator⁻¹)
      (encoding.encode (denominator * numerator)) 0 width = encoding.encode numerator := by
  rw [encoded_product, ← mul_assoc, inv_mul_cancel₀ nonzero, one_mul]

/-- The native product recomputes any erased numerator of division without inverting the slope. -/
theorem encoded_division_recompute [Fact modulus.Prime]
    (encoding : BinaryResidueEncoding modulus width)
    (denominator numerator : ZMod modulus) (nonzero : denominator ≠ 0) :
    variableWordPrefix (encodedModulus encoding) (encoding.encode denominator)
      (encoding.encode (numerator * denominator⁻¹)) 0 width = encoding.encode numerator := by
  rw [encoded_product, mul_left_comm, mul_inv_cancel₀ nonzero, mul_one]

/-- Actual multiplication recomputation cancels exactly the original measured numerator phase. -/
theorem multiplication_cancels [Fact modulus.Prime]
    (encoding : BinaryResidueEncoding modulus width)
    (denominator numerator : ZMod modulus) (nonzero : denominator ≠ 0)
    (outcome : Fin (2 ^ width)) :
    (program width (encodedModulus encoding) (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome (encoding.encode numerator) •
          (NormalizedVector.ket
            ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
            ((VariableGidney.encoding width).encode
              (encoding.encode denominator⁻¹,
                encoding.encode (denominator * numerator), 0)))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
            ((VariableGidney.encoding width).encode
          (encoding.encode denominator⁻¹, encoding.encode (denominator * numerator), 0)))).vec := by
  have actual := program_cancels width (encodedModulus encoding) outcome
    (encoding.encode denominator⁻¹, encoding.encode (denominator * numerator), 0)
  simpa only [encoded_multiplication_recompute encoding denominator numerator nonzero] using actual

/-- Actual division recomputation cancels its measured numerator phase on the same full words. -/
theorem division_cancels [Fact modulus.Prime]
    (encoding : BinaryResidueEncoding modulus width)
    (denominator numerator : ZMod modulus) (nonzero : denominator ≠ 0)
    (outcome : Fin (2 ^ width)) :
    (program width (encodedModulus encoding) (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome (encoding.encode numerator) •
          (NormalizedVector.ket
            ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
            ((VariableGidney.encoding width).encode
              (encoding.encode denominator,
                encoding.encode (numerator * denominator⁻¹), 0)))).vec) =
      (NormalizedVector.ket
        ((QubitLayout.canonical (VariableGidney.encoding width).width).basisEquiv.symm
            ((VariableGidney.encoding width).encode
          (encoding.encode denominator, encoding.encode (numerator * denominator⁻¹), 0)))).vec := by
  have actual := program_cancels width (encodedModulus encoding) outcome
    (encoding.encode denominator, encoding.encode (numerator * denominator⁻¹), 0)
  simpa only [encoded_division_recompute encoding denominator numerator nonzero] using actual

end

end QuantumAlg.MeasuredUncompute.NativeProductCorrection
