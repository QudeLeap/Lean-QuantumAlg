/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Frame
import all QuantumAlg.Util.Nat.FixedWidth.Radix
import all QuantumAlg.Util.FinPow

/-!
# Original exponent bits at the literal full and tail window positions

These mathematical labels specify the current bank; they are not a circuit
for preparing or recycling it. The three-bit tail occupies the first three
MSB-first address systems. Its twelve remaining systems are arbitrary saved
labels, rather than additional zeros or missing physical systems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

/-- Place a current MSB-first payload beside all remaining original address systems. -/
def packAddress {width : Nat} (bounded : width ≤ 15) (payload : Fin (2 ^ width))
    (saved : Fin (2 ^ (15 - width))) : Address :=
  ⟨(prodEquiv (payload, saved)).val, (prodEquiv (payload, saved)).isLt.trans_eq
    (congrArg (fun count : Nat => 2 ^ count) (by omega : width + (15 - width) = 15))⟩

lemma packAddress_bit {width : Nat} (bounded : width ≤ 15) (payload : Fin (2 ^ width))
    (saved : Fin (2 ^ (15 - width))) (index : Fin width) :
    (packAddress bounded payload saved).val.testBit (14 - index.val) =
      payload.val.testBit index.rev.val := by
  have position : 14 - index.val = (15 - width) + index.rev.val := by
    have within := index.isLt
    simp only [Fin.val_rev]
    omega
  change (prodEquiv (payload, saved)).val.testBit (14 - index.val) = _
  rw [position]
  exact prodEquiv_testBit_left payload saved index.rev

lemma packAddress_saved {width : Nat} (bounded : width ≤ 15) (payload : Fin (2 ^ width))
    (saved : Fin (2 ^ (15 - width))) (index : Fin (15 - width)) :
    (packAddress bounded payload saved).val.testBit index.val = saved.val.testBit index.val :=
  prodEquiv_testBit_right payload saved index

def fullAddress (value : Nat) (window : Fin 16) : Address :=
  ⟨QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value window.val % 2 ^ 15,
    Nat.mod_lt _ (Nat.two_pow_pos 15)⟩

def fullPosition (window : Fin 16) (index : Fin 15) : Fin 260 :=
  ⟨16 * window.val + index.rev.val, by
    have windowBound := window.isLt
    have bitBound := index.rev.isLt
    omega⟩

def fullTopPosition (window : Fin 16) : Fin 260 :=
  ⟨16 * window.val + 15, by have bound := window.isLt; omega⟩

lemma fullAddress_bit (value : Nat) (window : Fin 16) (index : Fin 15) :
    (fullAddress value window).val.testBit index.rev.val =
      value.testBit (fullPosition window index).val := by
  change (QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value window.val % 2 ^ 15).testBit
    index.rev.val = value.testBit (16 * window.val + index.rev.val)
  rw [Nat.testBit_mod_two_pow, decide_eq_true index.rev.isLt, Bool.true_and]
  exact QuantumAlg.Nat.FixedWidth.Radix.binary_digit_bit 16 value window.val
    ⟨index.rev.val, by omega⟩

lemma fullAddress_get (state : Frame.Raw) (value : Nat) (window : Fin 16) (index : Fin 15) :
    (addressBit index).get (state, fullAddress value window) =
      value.testBit (fullPosition window index).val := by
  rw [addressBit_get]
  have position : 14 - index.val = index.rev.val := by
    simp only [Fin.val_rev]
    omega
  rw [position]
  exact fullAddress_bit value window index

lemma fullTop_bit (value : Nat) (window : Fin 16) :
    (QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value window.val).testBit 15 =
      value.testBit (fullTopPosition window).val :=
  QuantumAlg.Nat.FixedWidth.Radix.binary_digit_bit 16 value window.val ⟨15, by omega⟩

def tailPayload (value : Nat) : Fin (2 ^ 3) :=
  ⟨QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value 16 % 2 ^ 3,
    Nat.mod_lt _ (Nat.two_pow_pos 3)⟩

def tailAddress (value : Nat) (saved : Fin (2 ^ 12)) : Address :=
  packAddress (width := 3) (by omega) (tailPayload value) saved

def tailPosition (index : Fin 3) : Fin 260 :=
  ⟨256 + index.rev.val, by have within := index.rev.isLt; omega⟩

def tailTopPosition : Fin 260 := ⟨259, by omega⟩

lemma tailAddress_bit (value : Nat) (saved : Fin (2 ^ 12)) (index : Fin 3) :
    (tailAddress value saved).val.testBit (14 - index.val) =
      value.testBit (tailPosition index).val := by
  refine (packAddress_bit (width := 3) (by omega) (tailPayload value) saved index).trans ?_
  change (QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value 16 % 2 ^ 3).testBit
    index.rev.val = value.testBit (256 + index.rev.val)
  rw [Nat.testBit_mod_two_pow, decide_eq_true index.rev.isLt, Bool.true_and]
  exact QuantumAlg.Nat.FixedWidth.Radix.binary_digit_bit 16 value 16
    ⟨index.rev.val, by omega⟩

lemma tailAddress_get (state : Frame.Raw) (value : Nat) (saved : Fin (2 ^ 12))
    (index : Fin 3) :
    (addressBit ⟨index.val, by omega⟩).get (state, tailAddress value saved) =
      value.testBit (tailPosition index).val :=
  tailAddress_bit value saved index

lemma tailAddress_saved (value : Nat) (saved : Fin (2 ^ 12)) (index : Fin 12) :
    (tailAddress value saved).val.testBit index.val = saved.val.testBit index.val :=
  packAddress_saved (width := 3) (by omega) (tailPayload value) saved index

lemma tailTop_bit (value : Nat) :
    (QuantumAlg.Nat.FixedWidth.Radix.digit (2 ^ 16) value 16).testBit 3 =
      value.testBit tailTopPosition.val :=
  QuantumAlg.Nat.FixedWidth.Radix.binary_digit_bit 16 value 16 ⟨3, by omega⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
