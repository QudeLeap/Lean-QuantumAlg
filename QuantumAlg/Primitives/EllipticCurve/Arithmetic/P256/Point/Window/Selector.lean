/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Wires
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector
import all Init.Data.BitVec.Lemmas

/-!
# Actual table selector positions inside the original window bank

The selected stream bit supplies the original top control. The remaining
address is the current MSB-first suffix. Prefix work borrows the first
fifteen systems of the existing scan pool, while inversion is idle. No
selector coordinate uses N or the other coherent stream bit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

def streamBit (stream : Fin 2) : EncodedBit encoding :=
  if stream.val = 0 then firstStreamBit else secondStreamBit

lemma streamBit_wire (stream : Fin 2) :
    (streamBit stream).wire.val = if stream.val = 0 then 836 else 838 := by
  unfold streamBit
  split
  · exact firstStreamBit_wire
  · exact secondStreamBit_wire

/-- Ten address-pool systems followed by five original prefix-pool systems. -/
def poolPrefixBit (index : Fin 15) : EncodedBit encoding :=
  if first : index.val < 10 then
    pointBit (Frame.scanBit (MAU.Inversion.SharedEEA.Scanned.addressBit 256
      ⟨index.val, by change index.val < 10; exact first⟩))
  else
    pointBit (Frame.scanBit (MAU.Inversion.SharedEEA.Scanned.prefixBit 256
      ⟨index.val - 10, by change index.val - 10 < 10; omega⟩))

lemma poolPrefixBit_wire (index : Fin 15) :
    (poolPrefixBit index).wire.val = 559 + index.val := by
  have sourceWidth : (MAU.Inversion.SharedEEA.encoding 256).width = 559 := by
    rw [MAU.Inversion.SharedEEA.encoding_width]
    decide
  unfold poolPrefixBit
  split
  · rw [pointBit_wire, Frame.scanBit_wire,
      MAU.Inversion.SharedEEA.Scanned.addressBit_wire, sourceWidth]
  · rw [pointBit_wire, Frame.scanBit_wire,
      MAU.Inversion.SharedEEA.Scanned.prefixBit_wire, sourceWidth]
    change 559 + 10 + (index.val - 10) = _
    omega

lemma poolPrefixBit_clean (index : Fin 15) (state : Raw)
    (clean : Frame.CleanPool state.1) : (poolPrefixBit index).get state = false := by
  have pool : state.1.1.1.2 = (0, (0, false)) := clean
  unfold poolPrefixBit
  split
  · rw [pointBit_get, Frame.scanBit_get,
      MAU.Inversion.SharedEEA.Scanned.addressBit_get, pool]
    exact BitVec.getMsbD_zero
  · rw [pointBit_get, Frame.scanBit_get,
      MAU.Inversion.SharedEEA.Scanned.prefixBit_get, pool]
    exact BitVec.getMsbD_zero

def selectorStack (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) : EncodedBit encoding :=
  if index.val = 0 then streamBit stream
  else poolPrefixBit ⟨index.val - 1, by omega⟩

lemma selectorStack_wire (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) :
    (selectorStack stream width bounded index).wire.val =
      if index.val = 0 then (if stream.val = 0 then 836 else 838)
      else 559 + (index.val - 1) := by
  unfold selectorStack
  split
  · exact streamBit_wire stream
  · exact poolPrefixBit_wire _

/-- Both the full and tail actual lookup frames use only this same physical bank. -/
def selector (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    SelectorFrame encoding width where
  address index := addressBit ⟨index.val, by omega⟩
  stack := selectorStack stream width bounded
  addressDistinct := by
    intro left right same
    apply Fin.ext
    exact congrArg (fun index : Fin 15 => index.val) (addressBit_injective same)
  stackDistinct := by
    intro left right same
    apply Fin.ext
    have positions := congrArg Fin.val same
    rw [selectorStack_wire, selectorStack_wire] at positions
    have leftBound := left.isLt
    have rightBound := right.isLt
    split_ifs at positions <;> omega
  separate := by
    intro addressIndex stackIndex same
    have positions := congrArg Fin.val same
    rw [addressBit_wire, selectorStack_wire] at positions
    have stackBound := stackIndex.isLt
    split_ifs at positions <;> omega

def fullSelector (stream : Fin 2) : SelectorFrame encoding 15 := selector stream 15 (by omega)

def tailSelector (stream : Fin 2) : SelectorFrame encoding 3 := selector stream 3 (by omega)

lemma selector_root (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    (selector stream width bounded).stack 0 = streamBit stream := rfl

lemma selector_prefix_clean (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin width) (state : Raw) (clean : Frame.CleanPool state.1) :
    ((selector stream width bounded).stack index.succ).get state = false := by
  change (selectorStack stream width bounded index.succ).get state = false
  unfold selectorStack
  rw [if_neg (by simp)]
  exact poolPrefixBit_clean _ state clean

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
