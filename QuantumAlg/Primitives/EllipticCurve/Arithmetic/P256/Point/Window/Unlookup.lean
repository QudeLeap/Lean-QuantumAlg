/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Selector
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Frame

/-!
# Original word reuse in the full and tail measured unlookup

The unary targets are actual subsets of the same result word after its
physical measurement and reset. The low address is least significant first;
the high address and full lookup address are most significant first. High
prefixes reuse the original scan pool. These are coordinate certificates,
without preparation or a claim that a caller has already reset a result.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

def resultWord (port : WordPort) : EncodedBit.Word encoding 256 :=
  ⟨fun index => pointBit (port.bit index)⟩

lemma resultWord_wire (port : WordPort) (index : Fin 256) :
    ((resultWord port).bit index).wire.val = port.physicalIndex index :=
  WordPort.bit_wire port index

lemma resultWord_distinct (port : WordPort) :
    Function.Injective (fun index => ((resultWord port).bit index).wire) := by
  intro left right same
  apply WordPort.bit_index_injective port
  apply Fin.ext
  exact congrArg (fun wire : Fin encoding.width => wire.val) same

lemma resultWord_address (port : WordPort) (index : Fin 256) (address : Fin 15) :
    ((resultWord port).bit index).wire ≠ (addressBit address).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, addressBit_wire] at positions
  have bound := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

lemma resultWord_stack (port : WordPort) (index : Fin 256) (stream : Fin 2)
    (width : Nat) (bounded : width ≤ 15) (stack : Fin (width + 1)) :
    ((resultWord port).bit index).wire ≠ (selectorStack stream width bounded stack).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [resultWord_wire, selectorStack_wire] at positions
  have wordBound := index.isLt
  have stackBound := stack.isLt
  split_ifs at positions <;> cases port <;>
    simp only [WordPort.physicalIndex] at positions <;> omega

def lowAddress (highRemaining lowWidth : Nat) (bounded : highRemaining + lowWidth ≤ 15)
    (index : Fin lowWidth) : EncodedBit encoding :=
  addressBit ⟨highRemaining + lowWidth - 1 - index.val, by omega⟩

lemma lowAddress_distinct (highRemaining lowWidth : Nat)
    (bounded : highRemaining + lowWidth ≤ 15) :
    Function.Injective (fun index => (lowAddress highRemaining lowWidth bounded index).wire) := by
  intro left right same
  apply Fin.ext
  have addresses := congrArg (fun index : Fin 15 => index.val) (addressBit_injective same)
  change highRemaining + lowWidth - 1 - left.val =
    highRemaining + lowWidth - 1 - right.val at addresses
  have leftBound := left.isLt
  have rightBound := right.isLt
  omega

private def lowResult (lowWidth : Nat) (bounded : lowWidth ≤ 8) :
    Fin (2 ^ lowWidth) ↪ Fin 256 where
  toFun index := ⟨index.val, by
    have limit : 2 ^ lowWidth ≤ 256 :=
      Nat.pow_le_pow_right Nat.zero_lt_two bounded
    omega⟩
  inj' := by
    intro left right same
    exact Fin.ext (congrArg (fun index : Fin 256 => index.val) same)

def unary (port : WordPort) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8) :
    UnaryFrame encoding lowWidth where
  address := lowAddress highRemaining lowWidth addressBound
  target index := (resultWord port).bit (lowResult lowWidth lowBound index)
  addressDistinct := lowAddress_distinct highRemaining lowWidth addressBound
  targetDistinct := by
    intro left right same
    exact (lowResult lowWidth lowBound).injective (resultWord_distinct port same)
  outside := by
    intro address index
    exact (resultWord_address port _ _).symm

/-- The original reset result systems and shared prefixes meet every actual unlookup separation. -/
def unlookup (stream : Fin 2) (port : WordPort) (highRemaining lowWidth : Nat)
    (addressBound : highRemaining + lowWidth ≤ 15) (lowBound : lowWidth ≤ 8) :
    UnlookupFrame encoding 256 lowWidth highRemaining where
  result := resultWord port
  resultDistinct := resultWord_distinct port
  low := unary port highRemaining lowWidth addressBound lowBound
  lowResult := lowResult lowWidth lowBound
  lowResultWire _ := rfl
  high := selector stream highRemaining (by omega)
  lowAddressResult := by
    intro address resultIndex
    exact (resultWord_address port resultIndex _).symm
  highAddressResult := by
    intro address resultIndex
    exact (resultWord_address port resultIndex _).symm
  highStackResult := by
    intro stack resultIndex
    exact (resultWord_stack port resultIndex stream highRemaining (by omega) stack).symm
  lowHighAddress := by
    intro lowIndex highIndex same
    have addresses := congrArg (fun index : Fin 15 => index.val) (addressBit_injective same)
    change highRemaining + lowWidth - 1 - lowIndex.val = highIndex.val at addresses
    have lowWithin := lowIndex.isLt
    have highWithin := highIndex.isLt
    omega
  lowHighStack := by
    intro lowIndex highStack same
    have positions := congrArg Fin.val same
    change (lowAddress highRemaining lowWidth addressBound lowIndex).wire.val =
      (selectorStack stream highRemaining (by omega) highStack).wire.val at positions
    dsimp only [lowAddress] at positions
    rw [addressBit_wire, selectorStack_wire] at positions
    have stackBound := highStack.isLt
    split_ifs at positions <;> omega

def fullUnlookup (stream : Fin 2) (port : WordPort) : UnlookupFrame encoding 256 8 7 :=
  unlookup stream port 7 8 (by omega) (by omega)

def tailUnlookup (stream : Fin 2) (port : WordPort) : UnlookupFrame encoding 256 2 1 :=
  unlookup stream port 1 2 (by omega) (by omega)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
