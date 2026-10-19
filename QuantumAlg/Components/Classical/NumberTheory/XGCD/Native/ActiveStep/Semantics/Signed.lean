/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Semantics.Remainder

/-!
# The original signed recurrence in actual extended-Euclidean storage

Every input coefficient is interpreted by the original two's-complement
decoder. Actual wrapping operations always represent the mathematical step
modulo the unchanged execution modulus. Exact decoding requires only the
two newly computed signed ranges; the rotated coefficients retain their
literal original words. Activity is proved independently of those ranges.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms ClassicalAlgorithms.NumberTheory

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma rawSignedRepresents_decoded
    (word : CShape.Word (PureXGCD.executionCoefficientWidth width)) :
    RawSignedRepresents word (decodeRawSignedWord word) := by
  have actual := ofInt_rawSignedRepresents (PureXGCD.executionCoefficientWidth width)
    (decodeRawSignedWord word)
  simpa only [decodeRawSignedWord, BoundedSigned.ofInt_toInt, BoundedSigned.encode_decode,
    fixedWidthEncode_decode_word] using actual

private lemma divisionQuotient_value (first second : CShape.Word width) :
    (CShape.divRem width width (.product second first)).first.toNat =
      second.toNat / first.toNat := by
  change (second.toNat / first.toNat) % CShape.wordModulus width = _
  exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt second.toNat_lt)

/-- All four actual coefficient words represent the original total mathematical step. -/
lemma xgcdNativeActiveBody_rawSignedRepresents
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (scratch : Cells ctx (activeScratchShapes width)) (scratchDistinct : scratch.Distinct)
    (cross : CrossSeparated cells scratch) (zero : CInputRef ctx (.unsignedWord width))
    (store : Store ctx) :
    let next := PureXGCD.step (storedState cells store)
    let final := activeBodyStore cells scratch zero store
    RawSignedRepresents (final.read (GCD.cellRead (firstLeftCell cells)))
        next.firstLeftCoefficient ∧
      RawSignedRepresents (final.read (GCD.cellRead (secondLeftCell cells)))
        next.secondLeftCoefficient ∧
      RawSignedRepresents (final.read (GCD.cellRead (firstRightCell cells)))
        next.firstRightCoefficient ∧
      RawSignedRepresents (final.read (GCD.cellRead (secondRightCell cells)))
        next.secondRightCoefficient := by
  have values := xgcdNativeActiveBody_coefficient_values
    cells distinct scratch scratchDistinct cross zero store
  have quotientRepresents : RawSignedRepresents
      (CShape.wordResize (PureXGCD.executionCoefficientWidth width)
        (CShape.divRem width width (.product
          (store.read (GCD.cellRead (secondCell cells)))
          (store.read (GCD.cellRead (firstCell cells))))).first)
      ((storedState cells store).quotient : Int) := by
    have actual := rawSignedRepresents_wordResize
      (signedWidth := PureXGCD.executionCoefficientWidth width)
      (CShape.divRem width width (.product
        (store.read (GCD.cellRead (secondCell cells)))
        (store.read (GCD.cellRead (firstCell cells))))).first
    rw [divisionQuotient_value] at actual
    exact actual
  dsimp only [PureXGCD.step, ClassicalAlgorithms.NumberTheory.XGCD.step, storedState]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [values.1]
    exact rawSignedRepresents_sub _ _ _ _
      (rawSignedRepresents_decoded (width := width)
        (store.read (GCD.cellRead (secondLeftCell cells))))
      (rawSignedRepresents_mulLow _ _ _ _ quotientRepresents
        (rawSignedRepresents_decoded (width := width)
          (store.read (GCD.cellRead (firstLeftCell cells)))))
  · rw [values.2.1]
    exact rawSignedRepresents_decoded (width := width)
      (store.read (GCD.cellRead (firstLeftCell cells)))
  · rw [values.2.2.1]
    exact rawSignedRepresents_sub _ _ _ _
      (rawSignedRepresents_decoded (width := width)
        (store.read (GCD.cellRead (secondRightCell cells))))
      (rawSignedRepresents_mulLow _ _ _ _ quotientRepresents
        (rawSignedRepresents_decoded (width := width)
          (store.read (GCD.cellRead (firstRightCell cells)))))
  · rw [values.2.2.2]
    exact rawSignedRepresents_decoded (width := width)
      (store.read (GCD.cellRead (firstRightCell cells)))

/-- In the original ranges, actual storage decodes to the original total XGCD step. -/
lemma xgcdNativeActiveBody_state
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (scratch : Cells ctx (activeScratchShapes width)) (scratchDistinct : scratch.Distinct)
    (cross : CrossSeparated cells scratch) (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys)
    (scratchZero : ∀ index : Fin 4, (cellAt scratch index).ref.key ∉ zero.storageKeys)
    (store : Store ctx)
    (leftRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      (PureXGCD.executionCoefficientWidth width)
      (PureXGCD.step (storedState cells store)).firstLeftCoefficient)
    (rightRange : ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
      (PureXGCD.executionCoefficientWidth width)
      (PureXGCD.step (storedState cells store)).firstRightCoefficient) :
    storedState cells (activeBodyStore cells scratch zero store) =
      PureXGCD.step (storedState cells store) := by
  have coefficients := xgcdNativeActiveBody_coefficient_values
    cells distinct scratch scratchDistinct cross zero store
  have represents := xgcdNativeActiveBody_rawSignedRepresents
    cells distinct scratch scratchDistinct cross zero store
  have remainders := xgcdNativeActiveBody_remainder_values
    cells distinct scratch scratchDistinct cross zero stateZero scratchZero store
  have firstLeft : decodeRawSignedWord
      ((activeBodyStore cells scratch zero store).read (GCD.cellRead (firstLeftCell cells))) =
      (PureXGCD.step (storedState cells store)).firstLeftCoefficient :=
    rawSignedRepresents_decode_eq _ _
      (ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_pos width)
      represents.1 leftRange
  have firstRight : decodeRawSignedWord
      ((activeBodyStore cells scratch zero store).read (GCD.cellRead (firstRightCell cells))) =
      (PureXGCD.step (storedState cells store)).firstRightCoefficient :=
    rawSignedRepresents_decode_eq _ _
      (ClassicalAlgorithms.NumberTheory.XGCD.executionCoefficientWidth_pos width)
      represents.2.2.1 rightRange
  unfold storedState
  rw [remainders.1, remainders.2.1, coefficients.2.1, coefficients.2.2.2,
    firstLeft, firstRight]
  rfl

/-- The refreshed actual activity bit agrees with the actual leading remainder. -/
lemma xgcdNativeActiveBody_activity
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (scratch : Cells ctx (activeScratchShapes width)) (scratchDistinct : scratch.Distinct)
    (cross : CrossSeparated cells scratch) (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys)
    (scratchZero : ∀ index : Fin 4, (cellAt scratch index).ref.key ∉ zero.storageKeys)
    (store : Store ctx) (zeroValue : (store.read zero).toNat = 0) :
    let final := activeBodyStore cells scratch zero store
    (final.read (GCD.cellRead (activeCell cells))).toBool =
      decide ((storedState cells final).first ≠ 0) := by
  have values := xgcdNativeActiveBody_remainder_values
    cells distinct scratch scratchDistinct cross zero stateZero scratchZero store
  dsimp only
  rw [values.2.2.1, zeroValue]
  change _ = decide (((activeBodyStore cells scratch zero store).read
    (GCD.cellRead (firstCell cells))).toNat ≠ 0)
  rw [values.1]

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
