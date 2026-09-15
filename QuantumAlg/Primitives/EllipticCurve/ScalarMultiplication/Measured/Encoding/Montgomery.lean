/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Initialization

/-!
# Original Montgomery coordinates through actual initialized pair conversion

The original Montgomery word is transported only across the stated equality
of word widths. Actual inverse-radix conversion yields ordinary field words;
actual radix conversion returns exactly the original Montgomery encoding.
Both directions retain all original exponent and reference values and the
preparation produced by the actual initialization.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute MeasuredPointAddition Allocation
open GenericPointAddition.InPlace

/-- The original Montgomery coordinate words and supplied exponents form the actual input basis. -/
def montgomeryInput {p : Nat} [Fact p.Prime] (fieldTail count : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (exponent : (exponents p.size count).register.Index) (x y : ZMod p) :
    (before p.size count).register.Index :=
  inputLabel p.size count exponent
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits x))
    (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
      (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits y))

/-- The supplied Montgomery input is exactly the radix-scaled ordinary field-word input. -/
theorem montgomeryInput_fieldWords {p : Nat} [Fact p.Prime] (fieldTail count : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (exponent : (exponents p.size count).register.Index) (x y : ZMod p) :
    montgomeryInput fieldTail count sameWidth fits exponent x y =
      inputLabel p.size count exponent
        (fieldWord ((2 : ZMod p) ^ fieldTail.succ * x))
        (fieldWord ((2 : ZMod p) ^ fieldTail.succ * y)) := by
  unfold montgomeryInput
  rw [montgomeryWord_fieldWord fieldTail sameWidth fits x,
    montgomeryWord_fieldWord fieldTail sameWidth fits y]

/-- Actual inverse-radix conversion recovers both ordinary coordinates and all initialization. -/
theorem pairOperator_fromMontgomery {p : Nat} [Fact p.Prime] (fieldTail count : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (exponent : (exponents p.size count).register.Index) (x y : ZMod p)
    {Reference : Register} (reference : Reference.Index) :
    (pairOperator p.size count (InPlaceTarget.modulusWord p)
      (Semantics.radixUnit p fieldTail.succ odd)⁻¹ Reference).applyVec
        (NormalizedVector.ket (initializedReadyBasis p count
          (montgomeryInput fieldTail count sameWidth fits exponent x y), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p count
        (inputLabel p.size count exponent (fieldWord x) (fieldWord y)), reference)).vec := by
  rw [montgomeryInput_fieldWords fieldTail count sameWidth fits exponent x y]
  have actual := pairOperator_initialized_fieldWords count
    (Semantics.radixUnit p fieldTail.succ odd)⁻¹ exponent
    ((2 : ZMod p) ^ fieldTail.succ * x) ((2 : ZMod p) ^ fieldTail.succ * y) reference
  have recovered (value : ZMod p) :
      ((Semantics.radixUnit p fieldTail.succ odd)⁻¹ : (ZMod p)ˣ) *
        ((2 : ZMod p) ^ fieldTail.succ * value) = value := by
    rw [← Semantics.radixUnit_coe p fieldTail.succ odd]
    exact Units.inv_mul_cancel_left (Semantics.radixUnit p fieldTail.succ odd) value
  rw [recovered x, recovered y] at actual
  exact actual

/-- Actual radix pair conversion restores the identical original Montgomery input representation. -/
theorem pairOperator_toMontgomery {p : Nat} [Fact p.Prime] (fieldTail count : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
    (exponent : (exponents p.size count).register.Index) (x y : ZMod p)
    {Reference : Register} (reference : Reference.Index) :
    (pairOperator p.size count (InPlaceTarget.modulusWord p)
      (Semantics.radixUnit p fieldTail.succ odd) Reference).applyVec
        (NormalizedVector.ket (initializedReadyBasis p count
          (inputLabel p.size count exponent (fieldWord x) (fieldWord y)), reference)).vec =
      (NormalizedVector.ket (initializedReadyBasis p count
        (montgomeryInput fieldTail count sameWidth fits exponent x y), reference)).vec := by
  have actual := pairOperator_initializedReadyBasis p count (Fact.out : Nat.Prime p).pos
    (Semantics.radixUnit p fieldTail.succ odd) exponent (fieldWord x) (fieldWord y)
    (ZMod.val_lt x) (ZMod.val_lt y) reference
  rw [unitProductWord_toMontgomery fieldTail sameWidth fits odd x,
    unitProductWord_toMontgomery fieldTail sameWidth fits odd y] at actual
  exact actual

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
