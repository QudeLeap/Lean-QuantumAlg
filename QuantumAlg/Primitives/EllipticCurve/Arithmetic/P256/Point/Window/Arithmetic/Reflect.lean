/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Reflect.Update
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.State.Update
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Arithmetic
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Whole original-window output of the actual retained-enable reflection

The real suffix program changes only numerical X and retains the complete
original address and all source coordinates. Its ordinary field value is
exactly the chronological -1-X operation when the original real F is true.
The existing A is the only clean-work premise of the native program law.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

/-- The same actual reflection replaces exactly X in the complete original window label. -/
lemma reflectionProgram_original_label (environment : OracleModel.empty.Interpretation)
    (state : Raw) (zero : Frame.work1 state.1 = MAU.Addition.TTK.Reflection.zero 256) :
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment (ket state) =
      ket (resultSetConstant (resultWord .work2)
        (Frame.work2 (Chain.Arithmetic.Reflect.step state.1)) state) := by
  let value := Frame.work2 (Chain.Arithmetic.Reflect.step state.1)
  have actual := Chain.Arithmetic.Reflect.program_apply_original environment state.1 zero
  have lifted := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    Frame.encoding addressEncoding Chain.Arithmetic.Reflect.program state.1
    (resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state.1)
    state.2 actual
  change
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment (ket state) =
      ket (resultSetConstant (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256)
        value state.1, state.2) at lifted
  have same := EncodedBit.Word.resultSetConstant_onProductLeft addressEncoding
    (⟨WordPort.work2.bit⟩ : EncodedBit.Word Frame.encoding 256) value state.1 state.2
  change resultSetConstant (resultWord .work2) value state = _ at same
  exact lifted.trans (congrArg ket same.symm)

/-- The actual original numerical reflection is its independent ordinary field operation. -/
lemma reflection_step_word (state : Frame.Raw) (value : ZMod modulus)
    (represented : Frame.work2 state = Residue.word value) :
    Frame.work2 (Chain.Arithmetic.Reflect.step state) =
      Residue.word (if Native.BorrowedControl.flag.get state then -1 - value else value) := by
  rw [Chain.Arithmetic.Reflect.step_work2, represented]
  cases Native.BorrowedControl.flag.get state with
  | false => rfl
  | true => exact Residue.reflected_word value

/-- The actual field output retains every other original physical coordinate. -/
lemma reflectionProgram_field_label (environment : OracleModel.empty.Interpretation)
    (state : Raw) (zero : Frame.work1 state.1 = MAU.Addition.TTK.Reflection.zero 256)
    (value : ZMod modulus) (represented : Frame.work2 state.1 = Residue.word value) :
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment (ket state) =
      ket (resultSetConstant (resultWord .work2)
        (Residue.word (if Native.BorrowedControl.flag.get state.1 then -1 - value else value))
        state) := by
  have actual := reflectionProgram_original_label environment state zero
  rw [reflection_step_word state.1 value represented] at actual
  exact actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
