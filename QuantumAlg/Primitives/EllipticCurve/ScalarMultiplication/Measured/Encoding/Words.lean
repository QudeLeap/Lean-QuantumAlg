/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Semantics
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Program

/-!
# Exact conversion between ordinary and Montgomery field words

The original Montgomery coordinate word and the measured ordinary coordinate
word are related by multiplication by the original radix unit. The reverse
conversion uses its inverse. The existing multiply, swap and inverse-compute
program implements both conversions with an exactly restored auxiliary word.

The width equality is explicit, and both clean actions start from canonical
field words. No zero-auxiliary claim is made for padded inputs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open MeasuredPointAddition MeasuredUncompute Nat.FixedWidth
open GenericPointAddition.InPlace

/-- Unit multiplication of an ordinary field word has the exact field interpretation. -/
theorem unitProductWord_fieldWord {p : Nat} [Fact p.Prime]
    (coefficient : (ZMod p)ˣ) (value : ZMod p) :
    unitProductWord (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
        coefficient (fieldWord value) =
      fieldWord ((coefficient : ZMod p) * value) := by
  apply Fin.ext
  exact (ZMod.val_mul (coefficient : ZMod p) value).symm

/-- The old Montgomery word is exactly the ordinary word of the radix-scaled field value. -/
theorem montgomeryWord_fieldWord {p : Nat} [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (value : ZMod p) :
    Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
        (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits value) =
      fieldWord ((2 : ZMod p) ^ fieldTail.succ * value) := by
  apply Fin.ext
  have residue := congrArg ZMod.val
    (Semantics.montgomeryWord_cast fieldTail p (Fact.out : Nat.Prime p).pos fits value)
  rw [ZMod.val_natCast_of_lt
    (Semantics.montgomeryWord_lt fieldTail p (Fact.out : Nat.Prime p).pos fits value)]
    at residue
  exact residue

/-- Multiplication by the original radix produces the unchanged Montgomery representation. -/
theorem unitProductWord_toMontgomery {p : Nat} [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (value : ZMod p) :
    unitProductWord (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
        (Semantics.radixUnit p fieldTail.succ odd) (fieldWord value) =
      Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
        (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits value) := by
  rw [unitProductWord_fieldWord, Semantics.radixUnit_coe,
    montgomeryWord_fieldWord fieldTail sameWidth fits value]

/-- Multiplication by the inverse original radix recovers the ordinary field word. -/
theorem unitProductWord_fromMontgomery {p : Nat} [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (value : ZMod p) :
    unitProductWord (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
        (Semantics.radixUnit p fieldTail.succ odd)⁻¹
        (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
          (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits value)) =
      fieldWord value := by
  rw [← unitProductWord_toMontgomery fieldTail sameWidth fits odd value]
  exact unitProductWord_inverse (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
    (Semantics.radixUnit p fieldTail.succ odd) (fieldWord value) (ZMod.val_lt value)

/-- The actual radix program converts an ordinary coordinate and restores its zero auxiliary. -/
theorem gidney_toMontgomery_clean {p : Nat} [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (value : ZMod p) :
    (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
        (Semantics.radixUnit p fieldTail.succ odd)).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical
        (MAU.Multiplication.Accumulate.Gidney.encoding p.size).width).basisEquiv.symm
        ((MAU.Multiplication.Accumulate.Gidney.encoding p.size).encode
          (fieldWord value, 0)))) =
      NormalizedVector.ket ((QubitLayout.canonical
        (MAU.Multiplication.Accumulate.Gidney.encoding p.size).width).basisEquiv.symm
        ((MAU.Multiplication.Accumulate.Gidney.encoding p.size).encode
          (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
            (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits value),
            0))) := by
  rw [MAU.Multiplication.Gidney.gidneyUnitMultiplication_clean p.size
    (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
    (Semantics.radixUnit p fieldTail.succ odd) (fieldWord value) (ZMod.val_lt value)]
  rw [unitProductWord_toMontgomery fieldTail sameWidth fits odd value]

/-- The actual inverse-radix program decodes a canonical Montgomery coordinate and cleans up. -/
theorem gidney_fromMontgomery_clean {p : Nat} [Fact p.Prime]
    (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
    (fits : p < 2 ^ fieldTail.succ) (odd : Odd p) (value : ZMod p) :
    (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
        (Semantics.radixUnit p fieldTail.succ odd)⁻¹).applyNormalized
      (NormalizedVector.ket ((QubitLayout.canonical
        (MAU.Multiplication.Accumulate.Gidney.encoding p.size).width).basisEquiv.symm
        ((MAU.Multiplication.Accumulate.Gidney.encoding p.size).encode
          (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
            (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits value),
            0)))) =
      NormalizedVector.ket ((QubitLayout.canonical
        (MAU.Multiplication.Accumulate.Gidney.encoding p.size).width).basisEquiv.symm
        ((MAU.Multiplication.Accumulate.Gidney.encoding p.size).encode
          (fieldWord value, 0))) := by
  rw [MAU.Multiplication.Gidney.gidneyUnitMultiplication_clean p.size
    (InPlaceTarget.modulusWord p) (Fact.out : Nat.Prime p).pos
    (Semantics.radixUnit p fieldTail.succ odd)⁻¹ _
    (Semantics.montgomeryWord_lt fieldTail p (Fact.out : Nat.Prime p).pos fits value)]
  rw [unitProductWord_fromMontgomery fieldTail sameWidth fits odd value]

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
