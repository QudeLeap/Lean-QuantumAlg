/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Converted.BankGoodColumns
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Initialization.Reset
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Words

/-!
# Original radix coefficient and the actual reset arithmetic label

The generic conversion columns specialize to the original Montgomery radix.
The same coefficient encodes the original seed in the actual leading reset.
No seed, good set, arithmetic circuit or caller condition is changed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualRadixWords

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement GenericPointAddition.InPlace
open MeasuredPointAddition
open MAU.Inversion.SharedEEA

variable {p : Nat} [Fact p.Prime]

/-- The original unit coefficient is exactly the radix already used by the reset seed. -/
lemma encodedWords_radixUnit (fieldTail : Nat) (odd : Odd p) (x y : ZMod p) :
    ConvertedBankGoodColumns.encodedWords (Semantics.radixUnit p fieldTail.succ odd) x y =
      (fieldWord ((2 : ZMod p) ^ fieldTail.succ * x),
        fieldWord ((2 : ZMod p) ^ fieldTail.succ * y)) := by
  simp only [ConvertedBankGoodColumns.encodedWords, Semantics.radixUnit_coe]

/-- Both original Montgomery words have precisely these two encoded field values. -/
lemma encodedWords_originalMontgomery (fieldTail : Nat)
    (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
    (odd : Odd p) (x y : ZMod p) :
    ConvertedBankGoodColumns.encodedWords (Semantics.radixUnit p fieldTail.succ odd) x y =
      (Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
          (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits x),
        Fin.cast (congrArg (fun width : Nat => 2 ^ width) sameWidth)
          (Semantics.montgomeryWord fieldTail p (Fact.out : Nat.Prime p).pos fits y)) := by
  rw [encodedWords_radixUnit,
    Encoding.montgomeryWord_fieldWord fieldTail sameWidth fits x,
    Encoding.montgomeryWord_fieldWord fieldTail sameWidth fits y]

/-- The actual reset arithmetic component is the same prepared radix-encoded seed. -/
lemma resetArithmeticLabel_prepared (E : PrimeFieldShortWeierstrass p)
    (fieldTail : Nat) (odd : Odd p) (seed : AffinePoint E) :
    Recovery.Initialization.resetArithmeticLabel E fieldTail seed =
      InPlaceTarget.preparedBasis p
        (ConvertedBankGoodColumns.encodedWords
          (Semantics.radixUnit p fieldTail.succ odd) seed.x seed.y).1
        (ConvertedBankGoodColumns.encodedWords
          (Semantics.radixUnit p fieldTail.succ odd) seed.x seed.y).2 := by
  rw [encodedWords_radixUnit]
  rfl

end

end ActualRadixWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
