/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate.Initial
import all QuantumAlg.Components.Encoded.BitGates.Word.Product

/-!
# Original numerical word setters on the complete initialized call label

The mathematical word setters used to describe actual query outcomes
agree with complete initialized labels. The real enable toggle is
cleared on the resulting label; no metadata or zero-pool premise is
added to the arithmetic caller.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open EncodedBit EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

private def finiteWord (width : Nat) : EncodedBit.Word (.finIdentity width) width :=
  ⟨fun index => BinaryLabelEncoding.finIdentityBit width (WireAddress.littleEndianWire index)⟩

private lemma finiteWord_get {width : Nat} (index : Fin width) (state : Fin (2 ^ width)) :
    ((finiteWord width).bit index).get state = state.val.testBit index.val := by
  change state.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private lemma finiteWord_distinct (width : Nat) :
    Function.Injective (fun index => ((finiteWord width).bit index).wire) := by
  intro first second same
  change WireAddress.littleEndianWire first = WireAddress.littleEndianWire second at same
  exact WireAddress.bitIndex_injective same

private lemma setFiniteWord {width : Nat} (value state : Fin (2 ^ width)) :
    resultSetConstant (finiteWord width) value state = value := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  exact (finiteWord_get index _).symm.trans
    (resultSetConstant_get (finiteWord width) (finiteWord_distinct width) value state index)

private def onRight {Left Right : Type} (left : BinaryLabelEncoding Left)
    {right : BinaryLabelEncoding Right} {width : Nat} (word : EncodedBit.Word right width) :
    EncodedBit.Word (.prod left right) width :=
  ⟨fun index => BinaryLabelEncoding.prodRightBit left right (word.bit index)⟩

private lemma xorConstant_onRight {Left Right : Type} (left : BinaryLabelEncoding Left)
    {right : BinaryLabelEncoding Right} {width : Nat} (word : EncodedBit.Word right width)
    (constant : Fin (2 ^ width)) (first : Left) (second : Right) :
    Word.xorConstantStep (onRight left word) constant (first, second) =
      (first, Word.xorConstantStep word constant second) := by
  rw [Word.xorConstantStep_eq_indicesStep, Word.xorConstantStep_eq_indicesStep]
  have fold (indices : List (Fin width)) (second : Right) :
      Word.xorConstantIndicesStep (onRight left word) indices (first, second) =
        (first, Word.xorConstantIndicesStep word indices second) := by
    induction indices generalizing second with
    | nil => rfl
    | cons index rest ih =>
        change Word.xorConstantIndicesStep (onRight left word) rest
            (first, (word.bit index).flip second) =
          (first, Word.xorConstantIndicesStep word rest ((word.bit index).flip second))
        exact ih _
  exact fold _ second

private lemma setConstant_onRight {Left Right : Type} (left : BinaryLabelEncoding Left)
    {right : BinaryLabelEncoding Right} {width : Nat} (word : EncodedBit.Word right width)
    (value : Fin (2 ^ width)) (first : Left) (second : Right) :
    resultSetConstant (onRight left word) value (first, second) =
      (first, resultSetConstant word value second) := by
  unfold resultSetConstant
  exact xorConstant_onRight left word _ first second

/-- The original Y word setter changes precisely Y in the complete physical label. -/
lemma resultSetConstant_withNumerator (value : Word) (state : Window.Raw) :
    resultSetConstant (Window.resultWord .numerator) value state = withNumerator state value := by
  change resultSetConstant
      (Word.onProductLeft Window.addressEncoding
        (Word.onProductLeft Frame.controlsEncoding
          (onRight (MAU.Inversion.SharedEEA.Scanned.encoding 256) (finiteWord 256))))
      value ((state.1.1, state.1.2), state.2) = _
  rw [Word.resultSetConstant_onProductLeft, Word.resultSetConstant_onProductLeft]
  have right : resultSetConstant
      (onRight (MAU.Inversion.SharedEEA.Scanned.encoding 256) (finiteWord 256)) value state.1.1 =
        (state.1.1.1, resultSetConstant (finiteWord 256) value state.1.1.2) :=
    setConstant_onRight _ _ value state.1.1.1 state.1.1.2
  rw [right, setFiniteWord]
  rfl

private lemma withNumerator_digit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) (state : Window.Raw) (value : Word) :
    (Window.Enable.digitBit stream width bounded index).get (withNumerator state value) =
      (Window.Enable.digitBit stream width bounded index).get state := by
  refine Fin.cases ?_ (fun _ => ?_) index
  · unfold Window.Enable.digitBit Window.streamBit
    split <;> rfl
  · rfl

private lemma enable_withNumerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (value : Word) :
    Window.Enable.step stream width bounded (withNumerator state value) =
      withNumerator (Window.Enable.step stream width bounded state) value := by
  have same :
      (∀ index, (Window.Enable.digitBit stream width bounded index).get
        (withNumerator state value) = false) ↔
      (∀ index, (Window.Enable.digitBit stream width bounded index).get state = false) :=
    forall_congr' (fun index => by rw [withNumerator_digit])
  unfold Window.Enable.step Window.Enable.toggleStep
  change (if ∀ index, (Window.Enable.digitBit stream width bounded index).get
      (withNumerator state value) = false then withNumerator state value
    else Window.Enable.outputBit.flip (withNumerator state value)) =
    withNumerator
      (if ∀ index, (Window.Enable.digitBit stream width bounded index).get state = false
        then state else Window.Enable.outputBit.flip state) value
  by_cases zero : ∀ index, (Window.Enable.digitBit stream width bounded index).get state = false
  · rw [if_pos (same.mpr zero), if_pos zero]
  · rw [if_neg (fun matched => zero (same.mp matched)), if_neg zero]
    rfl

attribute [local irreducible] modulus

/-- An updated numerator has the same full initialized call label, with no new premise. -/
lemma inputState_withNumerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input first second : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    withNumerator (inputState stream width bounded input first flags address)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second) =
      inputState stream width bounded input second flags address := by
  change withNumerator
      (Window.Enable.step stream width bounded (clearedInitial input first flags address)) _ =
    Window.Enable.step stream width bounded (clearedInitial input second flags address)
  exact (enable_withNumerator stream width bounded _ _).symm.trans
    (congrArg (Window.Enable.step stream width bounded)
      (clearedInitial_withNumerator input first second flags address))

lemma inputState_setNumerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input first second : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    resultSetConstant (Window.resultWord .numerator)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second)
        (inputState stream width bounded input first flags address) =
      inputState stream width bounded input second flags address :=
  (resultSetConstant_withNumerator _ _).trans
    (inputState_withNumerator stream width bounded input first second flags address)

/-- The real toggle clears F after the original Y update, returning the exact initializer. -/
lemma clearEnable_setNumerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input first second : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    Window.Enable.step stream width bounded
      (resultSetConstant (Window.resultWord .numerator)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) second)
        (inputState stream width bounded input first flags address)) =
      clearedInitial input second flags address :=
  (congrArg (Window.Enable.step stream width bounded)
    (inputState_setNumerator stream width bounded input first second flags address)).trans
      (inputState_clear stream width bounded input second flags address)

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
