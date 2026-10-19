/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Encoding
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Coefficient.Semantics

/-!
# Signed meaning of the actual coefficient update

The original modulo representation follows the exact store produced by the
four native instructions. The first coefficient becomes the previous second
coefficient minus the quotient times the previous first coefficient, and the
second retains the previous first coefficient. Exact two's-complement decoding
uses the original positive-width and signed-range hypotheses for those results.

The circuit's five internal separation conditions and its actual word width
are retained. Scratch contents remain arbitrary. These are one-step coefficient
laws, with no claim about an entire extended-Euclidean execution.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD

open Execution ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual two output words retain the original modular signed recurrence. -/
lemma xgcdCoefficientUpdate_rawSignedRepresents
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (firstSecond : first.key ≠ second.key)
    (productFirst : product.key ≠ first.key) (productSecond : product.key ≠ second.key)
    (updatedFirst : updated.key ≠ first.key) (secondUpdated : second.key ≠ updated.key)
    (store : Store ctx) (quotientValue firstValue secondValue : Int)
    (quotientRepresents : RawSignedRepresents (store.read quotient) quotientValue)
    (firstRepresents : RawSignedRepresents (store.read (coefficientRead first)) firstValue)
    (secondRepresents : RawSignedRepresents (store.read (coefficientRead second)) secondValue) :
    let final := coefficientUpdateStore quotient first second product updated store
    RawSignedRepresents (final.read (coefficientRead first))
        (secondValue - quotientValue * firstValue) ∧
      RawSignedRepresents (final.read (coefficientRead second)) firstValue := by
  have values := xgcdCoefficientUpdate_store_values quotient first second product updated
    firstSecond productFirst productSecond updatedFirst secondUpdated store
  dsimp only
  constructor
  · rw [values.1]
    exact rawSignedRepresents_sub _ _ secondValue (quotientValue * firstValue) secondRepresents
      (rawSignedRepresents_mulLow _ _ quotientValue firstValue
        quotientRepresents firstRepresents)
  · rw [values.2]
    exact firstRepresents

/-- Signed-range results decode exactly from the actual updated coefficient cells. -/
lemma xgcdCoefficientUpdate_decode
    (quotient : CInputRef ctx (.unsignedWord width))
    (first second product updated : CWriteRef ctx (.unsignedWord width))
    (firstSecond : first.key ≠ second.key)
    (productFirst : product.key ≠ first.key) (productSecond : product.key ≠ second.key)
    (updatedFirst : updated.key ≠ first.key) (secondUpdated : second.key ≠ updated.key)
    (store : Store ctx) (quotientValue firstValue secondValue : Int)
    (quotientRepresents : RawSignedRepresents (store.read quotient) quotientValue)
    (firstRepresents : RawSignedRepresents (store.read (coefficientRead first)) firstValue)
    (secondRepresents : RawSignedRepresents (store.read (coefficientRead second)) secondValue)
    (widthPositive : 0 < width)
    (firstRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      width (secondValue - quotientValue * firstValue))
    (secondRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable width firstValue) :
    let final := coefficientUpdateStore quotient first second product updated store
    (BoundedSigned.decode (decodeWord (final.read (coefficientRead first)))).toInt =
        secondValue - quotientValue * firstValue ∧
      (BoundedSigned.decode (decodeWord (final.read (coefficientRead second)))).toInt =
        firstValue := by
  have represents := xgcdCoefficientUpdate_rawSignedRepresents
    quotient first second product updated
    firstSecond productFirst productSecond updatedFirst secondUpdated
    store quotientValue firstValue secondValue
    quotientRepresents firstRepresents secondRepresents
  exact ⟨rawSignedRepresents_decode_eq _ _ widthPositive represents.1 firstRange,
    rawSignedRepresents_decode_eq _ _ widthPositive represents.2 secondRange⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD
