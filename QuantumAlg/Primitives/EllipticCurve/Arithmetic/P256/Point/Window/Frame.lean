/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Frame
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Original point bank with its fifteen retained window address systems

The actual bank has 854 systems. Both coherent stream bits are already
present as C and W. The fifteen appended systems carry only the current
window address, rather than either complete 260-bit exponent register.
No value or cleanliness premise changes the physical coordinates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

abbrev Address := Fin (2 ^ 15)

abbrev Raw := Frame.Raw × Address

def addressEncoding : BinaryLabelEncoding Address := .finIdentity 15

@[implicit_reducible]
def encoding : BinaryLabelEncoding Raw := .prod Frame.encoding addressEncoding

lemma encoding_width : encoding.width = 854 := by
  change Frame.encoding.width + 15 = 854
  rw [Frame.encoding_width]

section

attribute [local irreducible] Frame.encoding

lemma encoding_surjective : Function.Surjective encoding.encode :=
  Frame.product_total Frame.encoding addressEncoding Frame.encoding_surjective
    (fun label => ⟨label, rfl⟩)

end

/-- Retain an original point-system identity before the current window address. -/
def pointBit (bit : EncodedBit Frame.encoding) : EncodedBit encoding :=
  BinaryLabelEncoding.prodLeftBit Frame.encoding addressEncoding bit

lemma pointBit_wire (bit : EncodedBit Frame.encoding) :
    (pointBit bit).wire.val = bit.wire.val := rfl

lemma pointBit_get (bit : EncodedBit Frame.encoding) (state : Raw) :
    (pointBit bit).get state = bit.get state.1 := rfl

/-- Address order is physical and MSB first, as required by the actual table selector. -/
def addressBit (index : Fin 15) : EncodedBit encoding :=
  BinaryLabelEncoding.prodRightBit Frame.encoding addressEncoding
    (BinaryLabelEncoding.finIdentityBit 15 index)

lemma addressBit_wire (index : Fin 15) :
    (addressBit index).wire.val = 839 + index.val := by
  change Frame.encoding.width + index.val = _
  rw [Frame.encoding_width]

lemma addressBit_get (index : Fin 15) (state : Raw) :
    (addressBit index).get state = state.2.val.testBit (14 - index.val) := rfl

lemma addressBit_injective : Function.Injective (fun index => (addressBit index).wire) := by
  intro left right same
  apply Fin.ext
  have positions := congrArg Fin.val same
  rw [addressBit_wire, addressBit_wire] at positions
  omega

lemma point_address_disjoint (bit : EncodedBit Frame.encoding) (index : Fin 15) :
    (pointBit bit).wire ≠ (addressBit index).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [pointBit_wire, addressBit_wire] at positions
  have bounded := bit.wire.isLt
  have width := Frame.encoding_width
  omega

def firstStreamBit : EncodedBit encoding := pointBit Frame.pointControlBit

def secondStreamBit : EncodedBit encoding := pointBit Frame.workBit

def normalBit : EncodedBit encoding := pointBit Frame.normalBit

lemma firstStreamBit_wire : firstStreamBit.wire.val = 836 := Frame.pointControlBit_wire

lemma secondStreamBit_wire : secondStreamBit.wire.val = 838 := Frame.workBit_wire

lemma normalBit_wire : normalBit.wire.val = 837 := Frame.normalBit_wire

lemma firstStreamBit_get (state : Raw) : firstStreamBit.get state = state.1.2.1 := rfl

lemma secondStreamBit_get (state : Raw) : secondStreamBit.get state = state.1.2.2.2 := rfl

/-- The existing fifteen systems are retained by the same complete original point body. -/
def suffixProgram (body : Native.Circuit) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical encoding.width).toQuantum :=
  UnitaryCircuit.onBinaryPrefix 15 body

lemma suffixProgram_eventTrace (body : Native.Circuit) :
    (suffixProgram body).eventTrace = body.eventTrace :=
  UnitaryCircuit.unitaryCircuit_onBinaryPrefix_eventTrace 15 body

lemma suffixProgram_quantumTime (body : Native.Circuit) :
    (suffixProgram body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration :=
  UnitaryCircuit.unitaryCircuit_onBinaryPrefix_evaluatedEventDepth 15 _ body

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
