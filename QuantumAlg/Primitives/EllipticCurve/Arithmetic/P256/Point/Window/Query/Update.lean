/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Body
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Commutation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State.Update
import all QuantumAlg.Components.Encoded.BitGates.BitEquality.Readout
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Word
import all QuantumAlg.Components.Encoded.BitGates.Word.Product

/-!
# Exact original word update across both stream roles and enable directions

Both stream placements keep the original numerical word lenses. The
complete target-word update therefore passes through the same placement
and both real enable toggles. The full output label is the original
input with precisely that numerical target replaced; no other coordinate
or original correlation is discarded by a scalar readout claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

lemma streamPlacement_word_bit (stream : Fin 2) (port : WordPort) (index : Fin 256) :
    (streamPlacement stream).placeBit ((resultWord port).bit index) =
      (resultWord port).bit index := by
  apply EncodedBit.eq_of_get_eq encoding_surjective
  intro state
  change (port.bit index).get (sourceState stream state) = (port.bit index).get state.1
  rw [WordPort.bit_get, WordPort.bit_get, sourceState_word]

lemma streamPlacement_placeWord (stream : Fin 2) (port : WordPort) :
    (streamPlacement stream).placeWord (resultWord port) = resultWord port := by
  exact congrArg (fun bits : Fin 256 → EncodedBit encoding =>
    (⟨bits⟩ : EncodedBit.Word encoding 256))
    (funext fun index => streamPlacement_word_bit stream port index)

/-- The same full original setter under either static placement of the coherent stream roles. -/
lemma streamInput_setWord (stream : Fin 2) (port : WordPort) (value : Fin (2 ^ 256))
    (state : Frame.Raw) (address : Address) :
    resultSetConstant (resultWord port) value (streamInput stream state address) =
      streamInput stream
        (resultSetConstant (⟨port.bit⟩ : EncodedBit.Word Frame.encoding 256) value state)
        address := by
  have actual := (streamPlacement stream).resultSetConstant_placeWord
    (resultWord port) value (streamInput stream state address)
  rw [streamPlacement_placeWord, streamInput_grouping] at actual
  have component := EncodedBit.Word.resultSetConstant_onProductLeft addressEncoding
    (⟨port.bit⟩ : EncodedBit.Word Frame.encoding 256) value state address
  change resultSetConstant (resultWord port) value (state, address) = _ at component
  rw [component] at actual
  exact actual

/-- Changing the actual native numerical target changes exactly that original physical word. -/
lemma arithmeticInput_target_set (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    arithmeticInput stream width bounded ports source newTarget third retained address =
      resultSetConstant (resultWord ports.target) newTarget
        (arithmeticInput stream width bounded ports source target third retained address) := by
  unfold arithmeticInput
  rw [Native.arithmeticState_target_set ports source target newTarget third retained,
    ← streamInput_setWord, Enable.step_resultSetConstant_comm]

/-- The ordinary body's complete original label differs in exactly its numerical target. -/
lemma ordinaryStep_eq_target_set (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    let prepared := arithmeticSource stream width bounded state
    let retained := ((Placement.layout ports).grouping prepared).2.2
    ordinaryStep stream width bounded ports state =
      resultSetConstant (resultWord ports.target)
        (if (Native.BorrowedControl.controlBit ports).get retained then
          ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
          else ports.target.value prepared) state := by
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  let value := if (Native.BorrowedControl.controlBit ports).get retained then
    ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared
  have represented := state_eq_arithmeticInput stream width bounded ports state clean
  exact (arithmeticInput_target_set stream width bounded ports (ports.source.value prepared)
    (ports.target.value prepared) value (ports.multiplier.value prepared) retained state.2).trans
    (congrArg (resultSetConstant (resultWord ports.target) value) represented.symm)

/-- The exceptional body's independent N control also changes only the numerical target. -/
lemma exceptionalStep_eq_target_set (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (state : Raw) (clean : Frame.CleanPool state.1) :
    let prepared := arithmeticSource stream width bounded state
    let retained := ((Placement.layout ports).grouping prepared).2.2
    exceptionalStep stream width bounded ports state =
      resultSetConstant (resultWord ports.target)
        (if (Native.BorrowedControl.controlBit ports).get retained &&
            Bool.not ((Native.controlBit ports .normal).get retained) then
          ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
          else ports.target.value prepared) state := by
  let prepared := arithmeticSource stream width bounded state
  let retained := ((Placement.layout ports).grouping prepared).2.2
  let value := if (Native.BorrowedControl.controlBit ports).get retained &&
      Bool.not ((Native.controlBit ports .normal).get retained) then
    ModularAddition.modularSumWord (ports.source.value prepared) (ports.target.value prepared)
      else ports.target.value prepared
  have represented := state_eq_arithmeticInput stream width bounded ports state clean
  exact (arithmeticInput_target_set stream width bounded ports (ports.source.value prepared)
    (ports.target.value prepared) value (ports.multiplier.value prepared) retained state.2).trans
    (congrArg (resultSetConstant (resultWord ports.target) value) represented.symm)

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
