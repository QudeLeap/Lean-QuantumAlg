/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Frame
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Swap
import all QuantumAlg.Components.Encoded.BitGates.FullPlacement.Compose

/-!
# Two coherent stream roles on the same original bank

Only the static source roles of C and W are exchanged for the second
stream. Their physical identities, N, all original point data and the
fifteen address systems remain in the same bank. A program is actually
placed through this certificate; no runtime swap is executed. The other
coherent stream bit supplies the original body W, with arbitrary value.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open QuantumAlg.EncodedBit

private def identityPlacement {Data : Type} (encoding : BinaryLabelEncoding Data) :
    FullPlacement encoding encoding :=
  FullPlacement.ofGrouping encoding encoding (Equiv.refl _) (Equiv.refl _)
    (fun _ _ => rfl)

private lemma identityPlacement_wire {Data : Type} (encoding : BinaryLabelEncoding Data)
    (index : Fin encoding.width) : (identityPlacement encoding).mappedWire index = index := by
  apply Fin.ext
  change FullPlacement.wireAddress encoding encoding (Equiv.refl _) index.val = index.val
  exact dif_pos index.isLt

private def prependPlacement {Prefix Source Target : Type}
    (prefixEncoding : BinaryLabelEncoding Prefix) {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target} (whole : FullPlacement source target) :
    FullPlacement (.prod prefixEncoding source) (.prod prefixEncoding target) :=
  (FullPlacement.prodSwap prefixEncoding source).compose
    ((whole.appendRight prefixEncoding).compose (FullPlacement.prodSwap target prefixEncoding))

private lemma prependPlacement_grouping {Prefix Source Target : Type}
    (prefixEncoding : BinaryLabelEncoding Prefix) {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target} (whole : FullPlacement source target)
    (state : Prefix × Target) :
    (prependPlacement prefixEncoding whole).grouping state =
      (state.1, whole.grouping state.2) := rfl

private lemma prependPlacement_left {Prefix Source Target : Type}
    (prefixEncoding : BinaryLabelEncoding Prefix) {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target} (whole : FullPlacement source target)
    (index : Fin prefixEncoding.width) :
    (prependPlacement prefixEncoding whole).mappedWire
        (Fin.castAdd source.width index) =
      Fin.castAdd target.width index := by
  simp only [prependPlacement, FullPlacement.compose_mappedWire,
    FullPlacement.prodSwap_mappedWire_left, FullPlacement.appendRight_mappedWire_extra,
    FullPlacement.prodSwap_mappedWire_right]

private lemma prependPlacement_right {Prefix Source Target : Type}
    (prefixEncoding : BinaryLabelEncoding Prefix) {source : BinaryLabelEncoding Source}
    {target : BinaryLabelEncoding Target} (whole : FullPlacement source target)
    (index : Fin source.width) :
    (prependPlacement prefixEncoding whole).mappedWire
        (Fin.natAdd prefixEncoding.width index) =
      Fin.natAdd prefixEncoding.width (whole.mappedWire index) := by
  simp only [prependPlacement, FullPlacement.compose_mappedWire,
    FullPlacement.prodSwap_mappedWire_right, FullPlacement.appendRight_mappedWire_source,
    FullPlacement.prodSwap_mappedWire_left]

private def controlSwap : Frame.Controls ≃ Frame.Controls where
  toFun value := (value.2.2, (value.2.1, value.1))
  invFun value := (value.2.2, (value.2.1, value.1))
  left_inv _ := rfl
  right_inv _ := rfl

private def controlPlacement : FullPlacement Frame.controlsEncoding Frame.controlsEncoding :=
  FullPlacement.ofGrouping _ _ controlSwap (Equiv.swap (0 : Fin 3) (2 : Fin 3)) (by
    rintro ⟨first, normal, second⟩ index
    fin_cases index <;> cases first <;> cases normal <;> cases second <;> rfl)

private lemma controlPlacement_wire (index : Fin 3) :
    controlPlacement.mappedWire index = Equiv.swap (0 : Fin 3) 2 index := by
  apply Fin.ext
  change FullPlacement.wireAddress Frame.controlsEncoding Frame.controlsEncoding
    (Equiv.swap (0 : Fin 3) (2 : Fin 3)) index.val = _
  exact dif_pos index.isLt

private def pointSwapAt (width : Nat) :
    FullPlacement (Frame.encodingAt width) (Frame.encodingAt width) :=
  prependPlacement (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding width) controlPlacement

private lemma pointSwapAt_grouping (width : Nat)
    (state : MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data width × Frame.Controls) :
    (pointSwapAt width).grouping state =
      (state.1, (state.2.2.2, (state.2.2.1, state.2.1))) :=
  prependPlacement_grouping _ _ state

section

attribute [local irreducible] Frame.payloadWidth

private def pointSwap : FullPlacement Frame.encoding Frame.encoding :=
  pointSwapAt Frame.payloadWidth

private lemma pointSwap_grouping (state : Frame.Raw) :
    pointSwap.grouping state = (state.1, (state.2.2.2, (state.2.2.1, state.2.1))) :=
  pointSwapAt_grouping Frame.payloadWidth state

/-- Both streams use the same bank; only original C/W roles depend on the public stream index. -/
def streamPlacement (stream : Fin 2) : FullPlacement encoding encoding :=
  if stream.val = 0 then identityPlacement encoding
  else pointSwap.appendRight addressEncoding

lemma streamPlacement_grouping (stream : Fin 2) (state : Raw) :
    (streamPlacement stream).grouping state =
      if stream.val = 0 then state
      else ((state.1.1, (state.1.2.2.2, (state.1.2.2.1, state.1.2.1))), state.2) := by
  by_cases first : stream.val = 0
  · rw [streamPlacement, if_pos first, if_pos first]
    rfl
  · rw [streamPlacement, if_neg first, if_neg first]
    exact congrArg (fun point => (point, state.2)) (pointSwap_grouping state.1)

lemma streamPlacement_address (stream : Fin 2) (index : Fin 15) :
    (streamPlacement stream).mappedWire (addressBit index).wire = (addressBit index).wire := by
  by_cases first : stream.val = 0
  · rw [streamPlacement, if_pos first]
    exact identityPlacement_wire _ _
  · rw [streamPlacement, if_neg first]
    exact FullPlacement.appendRight_mappedWire_extra pointSwap addressEncoding index

/-- The whole accepted point body is physically placed for the selected coherent stream. -/
def program (stream : Fin 2) (body : Native.Circuit) :
    UnitaryCircuit AlgorithmGate.model .empty (QubitLayout.canonical encoding.width).toQuantum :=
  (streamPlacement stream).place (suffixProgram body)

lemma program_eventTrace (stream : Fin 2) (body : Native.Circuit) :
    (program stream body).eventTrace = body.eventTrace :=
  ((streamPlacement stream).place_eventTrace (suffixProgram body)).trans
    (suffixProgram_eventTrace body)

lemma program_quantumTime (stream : Fin 2) (body : Native.Circuit) :
    (program stream body).evaluatedEventDepth Resource.Event.quantumDuration =
      body.evaluatedEventDepth Resource.Event.quantumDuration :=
  ((streamPlacement stream).place_evaluatedEventDepth _ Resource.Event.quantumDuration).trans
    (suffixProgram_quantumTime body)

end

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
