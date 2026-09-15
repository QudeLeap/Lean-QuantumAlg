/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.Classical.Arithmetic
import all QuantumAlg.Util.FinPow
import Mathlib.Tactic

/-!
# Fixed-width terminal bit decoding

This quantum-free module fixes the width and bit order of terminal classical
data before it is interpreted as an unsigned word.  A fixed `Fin width → Bool`
input is intrinsically length-correct; the `List` entry point rejects every
other length.  No conversion truncates a natural number into a claimed word:
the optional canonical-word constructor checks the exact `2 ^ width` bound.
-/

section

namespace QuantumAlg
namespace ClassicalAlgorithms

namespace TerminalDecode

/-- The declared order of a fixed terminal bit sequence. -/
public inductive BitOrder where
  /-- Position zero is the most significant input bit. -/
  | bigEndian
  /-- Position zero is the least significant input bit. -/
  | littleEndian
deriving DecidableEq

/-- Fixed terminal bits together with their explicit decoding order. -/
structure Input (width : Nat) where
  /-- The declared interpretation of `bits`. -/
  order : BitOrder
  /-- Exactly `width` terminal bits. -/
  bits : Fin width → Bool

/-- A decoded terminal word is bounded by its declared width. -/
abbrev Output (width : Nat) := Word width

/-- Append one bit to a most-significant-bit-first natural accumulator. -/
def appendBit (accumulator : Nat) (bit : Bool) : Nat :=
  2 * accumulator + bit.toNat

/-- Head-recursive accumulator fold, in the same increasing-index order used
by a machine `forRange`.  It is kept beside the mathematically convenient
last-recursive fold so routine proofs do not need a trace replay. -/
def accumulatorFold : (width : Nat) → Nat → (Fin width → Bool) → Nat
  | 0, accumulator, _bits => accumulator
  | width + 1, accumulator, bits =>
      accumulatorFold width (appendBit accumulator (bits 0))
        (bits ∘ Fin.succ)

private theorem accumulatorFold_eq_ofBits {width : Nat}
    (accumulator : Nat) (bits : Fin width → Bool) :
    accumulatorFold width accumulator bits =
      accumulator * 2 ^ width + Nat.ofBits (bits ∘ Fin.rev) := by
  induction width generalizing accumulator with
  | zero =>
      simp [accumulatorFold]
  | succ width inductionHypothesis =>
      simp only [accumulatorFold]
      rw [inductionHypothesis]
      have tailEq :
          (bits ∘ Fin.succ) ∘ Fin.rev =
            (bits ∘ Fin.rev) ∘ Fin.castSucc := by
        funext index
        simp only [Function.comp_apply]
        rw [Fin.rev_castSucc]
      have headEq : (bits ∘ Fin.rev) (Fin.last width) = bits 0 := by
        simp only [Function.comp_apply, Fin.rev_last]
      rw [tailEq, nat_ofBits_succ_last, headEq]
      simp only [appendBit, pow_succ]
      ring

/-- Execute a most-significant-bit-first fold from an explicit accumulator. -/
def bigEndianFoldFrom : (width : Nat) → Nat → (Fin width → Bool) → Nat
  | 0, accumulator, _bits => accumulator
  | width + 1, accumulator, bits =>
      appendBit
        (bigEndianFoldFrom width accumulator (bits ∘ Fin.castSucc))
        (bits (Fin.last width))

/-- Decode a fixed sequence whose position zero is its most significant bit. -/
def bigEndianFold {width : Nat} (bits : Fin width → Bool) : Nat :=
  bigEndianFoldFrom width 0 bits

private theorem bigEndianFoldFrom_eq_ofBits {width : Nat}
    (accumulator : Nat) (bits : Fin width → Bool) :
    bigEndianFoldFrom width accumulator bits =
      accumulator * 2 ^ width + Nat.ofBits (bits ∘ Fin.rev) := by
  induction width generalizing accumulator with
  | zero =>
      simp [bigEndianFoldFrom]
  | succ width inductionHypothesis =>
      simp only [bigEndianFoldFrom]
      rw [inductionHypothesis]
      have tailEq :
          (bits ∘ Fin.rev) ∘ Fin.succ =
            (bits ∘ Fin.castSucc) ∘ Fin.rev := by
        funext index
        simp only [Function.comp_apply]
        rw [Fin.rev_succ]
      have zeroEq : (bits ∘ Fin.rev) 0 = bits (Fin.last width) := by
        simp only [Function.comp_apply, Fin.rev_zero]
      have split :
          Nat.ofBits (bits ∘ Fin.rev) =
            2 * Nat.ofBits ((bits ∘ Fin.castSucc) ∘ Fin.rev) +
              (bits (Fin.last width)).toNat := by
        rw [Nat.ofBits_succ, tailEq, zeroEq]
      rw [split]
      simp only [appendBit, pow_succ]
      ring

/-- The accumulator fold agrees with the canonical little-endian `Nat.ofBits`
view after reversing a declared big-endian input. -/
theorem bigEndianFold_eq_ofBits {width : Nat} (bits : Fin width → Bool) :
    bigEndianFold bits = Nat.ofBits (bits ∘ Fin.rev) := by
  unfold bigEndianFold
  simpa using bigEndianFoldFrom_eq_ofBits 0 bits

/-- The head-recursive machine-order fold agrees with the canonical
big-endian mathematical fold. -/
theorem accumulatorFold_zero_eq_bigEndianFold {width : Nat}
    (bits : Fin width → Bool) :
    accumulatorFold width 0 bits = bigEndianFold bits := by
  rw [accumulatorFold_eq_ofBits, bigEndianFold_eq_ofBits]
  simp

/-- A big-endian fold of exactly `width` bits is intrinsically canonical. -/
theorem bigEndianFold_lt {width : Nat} (bits : Fin width → Bool) :
    bigEndianFold bits < modulus width := by
  rw [bigEndianFold_eq_ofBits]
  simpa [modulus] using Nat.ofBits_lt_two_pow (bits ∘ Fin.rev)

/-- Decode a terminal input according to its declared bit order. -/
def decodeNat {width : Nat} : Input width → Nat
  | ⟨.bigEndian, bits⟩ => bigEndianFold bits
  | ⟨.littleEndian, bits⟩ => Nat.ofBits bits

/-- Bits in the left-to-right order consumed by a shift-and-append
accumulator.  Little-endian input is reversed before that accumulator sees
it; the declaration remains explicit instead of being inferred from a list. -/
def accumulatorBits {width : Nat} (order : BitOrder) (bits : Fin width → Bool) :
    Fin width → Bool :=
  match order with
  | .bigEndian => bits
  | .littleEndian => bits ∘ Fin.rev

/-- Both declared orders reduce to one explicit accumulator fold. -/
theorem decodeNat_eq_bigEndianFold_accumulatorBits {width : Nat}
    (input : Input width) :
    decodeNat input = bigEndianFold (accumulatorBits input.order input.bits) := by
  cases input with
  | mk order bits =>
      cases order with
      | bigEndian => rfl
      | littleEndian =>
          change Nat.ofBits bits = bigEndianFold (bits ∘ Fin.rev)
          rw [bigEndianFold_eq_ofBits]
          have hrev : (bits ∘ Fin.rev) ∘ Fin.rev = bits := by
            funext index
            simp only [Function.comp_apply]
            exact congrArg bits (Fin.rev_rev index)
          rw [hrev]

/-- Big-endian decoding is exactly the Core full-register convention. -/
@[simp] theorem decodeNat_bigEndian {width : Nat} (bits : Fin width → Bool) :
    decodeNat ({ order := .bigEndian, bits := bits } : Input width) =
      Nat.ofBits (bits ∘ Fin.rev) := by
  simpa [decodeNat] using bigEndianFold_eq_ofBits bits

/-- Little-endian decoding preserves the canonical order expected by
`Nat.ofBits`. -/
@[simp] theorem decodeNat_littleEndian {width : Nat} (bits : Fin width → Bool) :
    decodeNat ({ order := .littleEndian, bits := bits } : Input width) =
      Nat.ofBits bits :=
  rfl

/-- Every declared fixed-width decode is in the exact output range. -/
theorem decodeNat_lt {width : Nat} (input : Input width) :
    decodeNat input < modulus width := by
  cases input with
  | mk order bits =>
      cases order with
      | bigEndian =>
          simpa [decodeNat, modulus, bigEndianFold_eq_ofBits] using
            (Nat.ofBits_lt_two_pow (bits ∘ Fin.rev))
      | littleEndian =>
          simpa [decodeNat, modulus] using (Nat.ofBits_lt_two_pow bits)

/-- The intrinsic fixed-width result of terminal decoding. -/
def eval {width : Nat} (input : Input width) : Output width :=
  ⟨decodeNat input, by simpa [modulus] using decodeNat_lt input⟩

/-- Mathematical acceptance for one terminal decoder result. -/
def accepts {width : Nat} (input : Input width) (output : Output width) : Prop :=
  output.val = decodeNat input

/-- The executable decoder satisfies its exact natural-value contract. -/
theorem eval_accepts {width : Nat} (input : Input width) :
    accepts input (eval input) :=
  rfl

/-- The big-endian result is the full-register `Nat.ofBits` value. -/
@[simp] theorem eval_bigEndian_val {width : Nat} (bits : Fin width → Bool) :
    (eval ({ order := .bigEndian, bits := bits } : Input width)).val =
      Nat.ofBits (bits ∘ Fin.rev) := by
  exact decodeNat_bigEndian bits

/-- The canonical typed counterpart of a full-register terminal measurement
index.  It deliberately lives in the pure fixed-width layer so later machine
and measurement bridges can agree on one explicit big-endian convention. -/
def fullRegisterIndex {width : Nat} (bits : Fin width → Bool) : Output width :=
  eval ({ order := .bigEndian, bits := bits } : Input width)

/-- The typed full-register index has the Core terminal-measurement value. -/
@[simp] theorem fullRegisterIndex_val {width : Nat} (bits : Fin width → Bool) :
    (fullRegisterIndex bits).val = Nat.ofBits (bits ∘ Fin.rev) :=
  eval_bigEndian_val bits

/-- The little-endian result is the direct `Nat.ofBits` value. -/
@[simp] theorem eval_littleEndian_val {width : Nat} (bits : Fin width → Bool) :
    (eval ({ order := .littleEndian, bits := bits } : Input width)).val =
      Nat.ofBits bits := by
  exact decodeNat_littleEndian bits

/-- Width-zero decoding has the unique zero result for either declared order. -/
@[simp] theorem decodeNat_zero (order : BitOrder) (bits : Fin 0 → Bool) :
    decodeNat ({ order := order, bits := bits } : Input 0) = 0 := by
  cases order <;> simp [decodeNat, bigEndianFold, bigEndianFoldFrom]

/-- Encode a bounded word in one declared terminal bit order. -/
def encodeBits {width : Nat} (order : BitOrder) (word : Output width) :
    Fin width → Bool :=
  match order with
  | .bigEndian => fun index => word.val.testBit (Fin.rev index).val
  | .littleEndian => fun index => word.val.testBit index.val

/-- Decoding the fixed-width encoding of a word recovers that word exactly. -/
theorem eval_encodeBits {width : Nat} (order : BitOrder) (word : Output width) :
    eval ({ order := order, bits := encodeBits order word } : Input width) = word := by
  apply Fin.val_injective
  cases order with
  | bigEndian =>
      rw [eval_bigEndian_val]
      have hbits :
          (encodeBits .bigEndian word) ∘ Fin.rev =
            fun index : Fin width => word.val.testBit index.val := by
        funext index
        simp only [encodeBits, Function.comp_apply]
        apply congrArg word.val.testBit
        exact congrArg Fin.val (Fin.rev_rev index)
      rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt word.isLt]
  | littleEndian =>
      rw [eval_littleEndian_val, encodeBits, Nat.ofBits_testBit,
        Nat.mod_eq_of_lt word.isLt]

/-- A natural number is canonical for one word width precisely when it fits
without truncation. -/
def CanonicalNat (width value : Nat) : Prop :=
  value < modulus width

/-- Construct a fixed word only after checking its exact natural range. -/
def canonicalWord? (width value : Nat) : Option (Output width) :=
  if range : value < modulus width then
    some ⟨value, by simpa [modulus] using range⟩
  else none

/-- A noncanonical natural number is rejected rather than truncated. -/
theorem canonicalWord?_rejects {width value : Nat}
    (notCanonical : ¬ CanonicalNat width value) :
    canonicalWord? width value = none := by
  have outOfRange : ¬ value < modulus width := by
    simpa [CanonicalNat] using notCanonical
  simp [canonicalWord?, outOfRange]

/-- A canonical natural number is preserved exactly by the checked constructor. -/
theorem canonicalWord?_accepts {width value : Nat}
    (canonical : CanonicalNat width value) :
    ∃ output : Output width,
      canonicalWord? width value = some output ∧ output.val = value := by
  have inRange : value < modulus width := by
    simpa [CanonicalNat] using canonical
  refine ⟨⟨value, by simpa [modulus] using inRange⟩, ?_, rfl⟩
  simp [canonicalWord?, inRange]

/-- Every fixed-input decoder result is canonical for its declared width. -/
theorem eval_canonical {width : Nat} (input : Input width) :
    CanonicalNat width (eval input).val := by
  simpa [CanonicalNat, eval] using decodeNat_lt input

/-- Check that an external list has exactly the declared fixed width before it
is made available as a terminal bit function. -/
def fixedBits? (width : Nat) (raw : List Bool) : Option (Fin width → Bool) :=
  if lengthEq : raw.length = width then
    some fun index => raw.get ⟨index.val, by
      rw [lengthEq]
      exact index.isLt⟩
  else none

/-- Lists of the wrong width cannot be interpreted as fixed terminal bits. -/
theorem fixedBits?_rejects_wrong_length {width : Nat} {raw : List Bool}
    (wrongLength : raw.length ≠ width) :
    fixedBits? width raw = none := by
  simp [fixedBits?, wrongLength]

/-- Decode an external list only after its width check and its canonical word
check have both succeeded. -/
def decode? (width : Nat) (order : BitOrder) (raw : List Bool) :
    Option (Output width) :=
  match fixedBits? width raw with
  | none => none
  | some bits => canonicalWord? width
      (decodeNat ({ order := order, bits := bits } : Input width))

/-- The public list decoder rejects every malformed-width encoding. -/
theorem decode?_rejects_wrong_length {width : Nat} (order : BitOrder)
    {raw : List Bool} (wrongLength : raw.length ≠ width) :
    decode? width order raw = none := by
  simp [decode?, fixedBits?, wrongLength]

end TerminalDecode

end ClassicalAlgorithms
end QuantumAlg

end
