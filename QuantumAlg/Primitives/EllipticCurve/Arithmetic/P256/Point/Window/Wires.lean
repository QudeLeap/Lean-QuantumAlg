/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Stream

/-!
# Literal physical identities of the two stream placements

All original data and pool positions and all fifteen address positions keep
their physical identities. Only C and W source roles exchange for stream one.
The same map relocates every native leaf of the actual whole program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open QuantumAlg.EncodedBit

private abbrev originalEncoding :=
  MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding Frame.payloadWidth

def controlWire (index : Fin 3) : Fin encoding.width :=
  Fin.castAdd addressEncoding.width (Fin.natAdd originalEncoding.width index)

lemma controlWire_first : controlWire 0 = firstStreamBit.wire := rfl

lemma controlWire_normal : controlWire 1 = normalBit.wire := rfl

lemma controlWire_second : controlWire 2 = secondStreamBit.wire := rfl

lemma streamPlacement_controls (stream : Fin 2) (index : Fin 3) :
    (streamPlacement stream).mappedWire (controlWire index) =
      controlWire (if stream.val = 0 then index else Equiv.swap (0 : Fin 3) 2 index) := by
  by_cases first : stream.val = 0
  · rw [streamPlacement, if_pos first, if_pos first]
    exact identityPlacement_wire _ _
  · rw [streamPlacement, if_neg first, if_neg first]
    have appended := FullPlacement.appendRight_mappedWire_source pointSwap addressEncoding
      (Fin.natAdd originalEncoding.width index)
    have prepended := prependPlacement_right originalEncoding controlPlacement index
    have lifted := congrArg (Fin.castAdd addressEncoding.width) prepended
    have controls := congrArg (fun bit => Fin.castAdd addressEncoding.width
      (Fin.natAdd originalEncoding.width bit)) (controlPlacement_wire index)
    exact appended.trans (lifted.trans controls)

lemma streamPlacement_first (stream : Fin 2) :
    (streamPlacement stream).mappedWire firstStreamBit.wire =
      if stream.val = 0 then firstStreamBit.wire else secondStreamBit.wire := by
  rw [← controlWire_first, streamPlacement_controls]
  by_cases first : stream.val = 0
  · rw [if_pos first, if_pos first]
  · rw [if_neg first, if_neg first, Equiv.swap_apply_left]
    rfl

lemma streamPlacement_second (stream : Fin 2) :
    (streamPlacement stream).mappedWire secondStreamBit.wire =
      if stream.val = 0 then secondStreamBit.wire else firstStreamBit.wire := by
  rw [← controlWire_second, streamPlacement_controls]
  by_cases first : stream.val = 0
  · rw [if_pos first, if_pos first]
  · rw [if_neg first, if_neg first, Equiv.swap_apply_right]
    rfl

lemma streamPlacement_normal (stream : Fin 2) :
    (streamPlacement stream).mappedWire normalBit.wire = normalBit.wire := by
  rw [← controlWire_normal, streamPlacement_controls]
  by_cases first : stream.val = 0
  · rw [if_pos first]
  · rw [if_neg first]
    rfl

def originalWire (index : Fin originalEncoding.width) : Fin encoding.width :=
  Fin.castAdd addressEncoding.width (Fin.castAdd Frame.controlsEncoding.width index)

/-- Original A/X/Y, padding, history and the complete pool use their exact original positions. -/
lemma streamPlacement_original (stream : Fin 2) (index : Fin originalEncoding.width) :
    (streamPlacement stream).mappedWire (originalWire index) = originalWire index := by
  by_cases first : stream.val = 0
  · rw [streamPlacement, if_pos first]
    exact identityPlacement_wire _ _
  · rw [streamPlacement, if_neg first]
    have appended := FullPlacement.appendRight_mappedWire_source pointSwap addressEncoding
      (Fin.castAdd Frame.controlsEncoding.width index)
    have prepended := prependPlacement_left originalEncoding controlPlacement index
    exact appended.trans (congrArg (Fin.castAdd addressEncoding.width) prepended)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
