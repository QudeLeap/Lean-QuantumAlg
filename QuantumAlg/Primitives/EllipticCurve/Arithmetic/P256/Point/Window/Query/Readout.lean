/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Arithmetic
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Address
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.State
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Cycle.Graph

/-!
# Original query graph retained by the actual arithmetic coordinates

The actual ordinary and exceptional additions change their target word.
Their complete source word, selected original stream bit and full address
remain unchanged. The same-table graph therefore survives the arithmetic
and the two paid enable directions, including every unused tail bit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

lemma streamInput_word (stream : Fin 2) (port : WordPort)
    (state : Frame.Raw) (address : Address) :
    port.value (streamInput stream state address).1 = port.value state := by
  have actual := sourceState_word stream port (streamInput stream state address)
  simp only [sourceState, streamInput_grouping] at actual
  exact actual.symm

lemma streamInput_streamBit (stream : Fin 2) (state : Frame.Raw) (address : Address) :
    (streamBit stream).get (streamInput stream state address) =
      Frame.pointControlBit.get state := by
  rw [streamInput_eq, streamBit]
  split <;> rfl

lemma enable_result_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (port : WordPort) (index : Fin 256) (state : Raw) :
    ((resultWord port).bit index).get (Enable.step stream width bounded state) =
      ((resultWord port).bit index).get state := by
  apply Enable.step_other
  intro same
  have positions := congrArg Fin.val same
  rw [Enable.outputBit_wire, resultWord_wire] at positions
  have within := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

lemma enable_stream_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Raw) :
    (streamBit stream).get (Enable.step stream width bounded state) =
      (streamBit stream).get state := by
  simpa only [Enable.digitBit, Fin.cases_zero] using
    Enable.step_digit stream width bounded (0 : Fin (width + 1)) state

lemma enable_address_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin 15) (state : Raw) :
    (addressBit index).get (Enable.step stream width bounded state) =
      (addressBit index).get state := by
  apply Enable.step_other
  intro same
  have positions := congrArg Fin.val same
  rw [Enable.outputBit_wire, addressBit_wire] at positions
  omega

/-- These are the complete input coordinates of both actual paid addition laws. -/
def arithmeticInput (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target third : Word)
    (retained : Placement.Rest ports) (address : Address) : Raw :=
  Enable.step stream width bounded
    (streamInput stream (Native.arithmeticState ports source target third retained) address)

lemma arithmeticInput_source_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target third : Word)
    (retained : Placement.Rest ports) (address : Address) (index : Fin 256) :
    ((resultWord ports.source).bit index).get
      (arithmeticInput stream width bounded ports source target third retained address) =
        source.val.testBit index.val := by
  rw [arithmeticInput, enable_result_get]
  change (ports.source.bit index).get
    (streamInput stream (Native.arithmeticState ports source target third retained) address).1 = _
  rw [WordPort.bit_get, streamInput_word, Native.arithmeticState_source]

lemma arithmeticInput_stream_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target third : Word)
    (retained : Placement.Rest ports) (address : Address) :
    (streamBit stream).get
      (arithmeticInput stream width bounded ports source target third retained address) =
        (Placement.savedPointControl ports).get retained := by
  rw [arithmeticInput, enable_stream_get, streamInput_streamBit]
  exact Native.arithmeticState_restBit ports Frame.pointControlBit
    (Placement.suffix_outside ports Frame.pointControlBit Frame.pointControlBit_wire.ge)
    source target third retained

lemma arithmeticInput_address_get (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (source target third : Word)
    (retained : Placement.Rest ports) (address : Address) (index : Fin 15) :
    (addressBit index).get
      (arithmeticInput stream width bounded ports source target third retained address) =
        address.val.testBit (14 - index.val) := by
  rw [arithmeticInput, enable_address_get, addressBit_get, streamInput_address]

/-- Changing only the real arithmetic target retains the original paid-unlookup graph. -/
lemma arithmeticInput_graph_update (stream : Fin 2) (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8)
    (ports : PortAssignment) (source target newTarget third : Word)
    (retained : Placement.Rest ports) (address : Address)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ 256))
    (graph : (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph
      table
      (arithmeticInput stream (highRemaining + lowWidth) bounded ports source target third
        retained address)) :
    (Window.unlookup stream ports.source highRemaining lowWidth bounded lowBound).Graph table
      (arithmeticInput stream (highRemaining + lowWidth) bounded ports source newTarget third
        retained address) := by
  apply EncodedBit.WindowLookup.UnlookupFrame.Graph.of_readouts _ table _ _ graph
  · intro index
    exact (arithmeticInput_source_get stream _ bounded ports source newTarget third
      retained address index).trans
      (arithmeticInput_source_get stream _ bounded ports source target third
        retained address index).symm
  · exact (arithmeticInput_stream_get stream _ bounded ports source newTarget third
      retained address).trans
      (arithmeticInput_stream_get stream _ bounded ports source target third
        retained address).symm
  · intro index
    exact (arithmeticInput_address_get stream _ bounded ports source newTarget third
      retained address ⟨index.val, by omega⟩).trans
      (arithmeticInput_address_get stream _ bounded ports source target third
        retained address ⟨index.val, by omega⟩).symm
  · intro index
    exact (arithmeticInput_address_get stream _ bounded ports source newTarget third
      retained address ⟨highRemaining + lowWidth - 1 - index.val, by omega⟩).trans
      (arithmeticInput_address_get stream _ bounded ports source target third
        retained address ⟨highRemaining + lowWidth - 1 - index.val, by omega⟩).symm

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
