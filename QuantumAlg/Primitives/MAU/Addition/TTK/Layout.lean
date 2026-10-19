/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Exact operand layouts for the TTK adder

The low-word interface contains two `n`-bit operands. The overflow interface
adds one output bit, with arbitrary initial value. Each source algorithm index
is little-endian; its physical wire is translated to the library's big-endian
convention [TTK09, qic-loglogaddition-quant.tex:285-290].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

open BinaryLabelEncoding

/-- Exactly two `n`-bit input/output words. -/
abbrev Registers (n : Nat) := Fin (2 ^ n) × Fin (2 ^ n)

/-- The two words and an explicit overflow output bit. -/
abbrev OverflowRegisters (n : Nat) := Registers n × Bool

/-- Canonical exact encoding of the two operands. -/
def encoding (n : Nat) : BinaryLabelEncoding (Registers n) :=
  prod (finIdentity n) (finIdentity n)

/-- Canonical exact encoding including the output carry bit. -/
def overflowEncoding (n : Nat) : BinaryLabelEncoding (OverflowRegisters n) :=
  prod (encoding n) bool

@[simp] lemma ttkEncoding_width (n : Nat) : (encoding n).width = 2 * n := by
  change n + n = 2 * n
  omega

@[simp] lemma ttkOverflowEncoding_width (n : Nat) :
    (overflowEncoding n).width = 2 * n + 1 := by
  change n + n + 1 = 2 * n + 1
  omega

/-- Addend bit `i`, counted from the least significant bit. -/
def leftBit (n : Nat) (i : Fin n) : EncodedBit (encoding n) :=
  prodLeftBit (finIdentity n) (finIdentity n)
    (finIdentityBit n (WireAddress.littleEndianWire i))

/-- Target bit `i`, counted from the least significant bit. -/
def rightBit (n : Nat) (i : Fin n) : EncodedBit (encoding n) :=
  prodRightBit (finIdentity n) (finIdentity n)
    (finIdentityBit n (WireAddress.littleEndianWire i))

lemma ttkLeftBit_get (n : Nat) (i : Fin n) (state : Registers n) :
    (leftBit n i).get state = state.1.val.testBit i.val := by
  change state.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire i)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

lemma ttkRightBit_get (n : Nat) (i : Fin n) (state : Registers n) :
    (rightBit n i).get state = state.2.val.testBit i.val := by
  change state.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire i)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

lemma ttkLeftBit_wire_val (n : Nat) (i : Fin n) :
    (leftBit n i).wire.val = n - 1 - i.val := rfl

lemma ttkRightBit_wire_val (n : Nat) (i : Fin n) :
    (rightBit n i).wire.val = n + (n - 1 - i.val) := rfl

lemma ttkLeftRight_disjoint (n : Nat) (i j : Fin n) :
    (leftBit n i).wire ≠ (rightBit n j).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [ttkLeftBit_wire_val, ttkRightBit_wire_val] at hval
  omega

lemma ttkLeftLeft_disjoint (n : Nat) (i j : Fin n) (hij : i ≠ j) :
    (leftBit n i).wire ≠ (leftBit n j).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [ttkLeftBit_wire_val, ttkLeftBit_wire_val] at hval
  apply hij
  apply Fin.ext
  omega

lemma ttkRightRight_disjoint (n : Nat) (i j : Fin n) (hij : i ≠ j) :
    (rightBit n i).wire ≠ (rightBit n j).wire := by
  intro h
  have hval := congrArg Fin.val h
  rw [ttkRightBit_wire_val, ttkRightBit_wire_val] at hval
  apply hij
  apply Fin.ext
  omega

/-- Lift an operand bit into the overflow layout without changing that operand. -/
def withOverflowBit {n : Nat} (bit : EncodedBit (encoding n)) :
    EncodedBit (overflowEncoding n) := prodLeftBit (encoding n) bool bit

/-- The explicit output carry wire. -/
def overflowBit (n : Nat) : EncodedBit (overflowEncoding n) :=
  prodRightBit (encoding n) bool boolBit

lemma ttkWithOverflowBit_get {n : Nat} (bit : EncodedBit (encoding n))
    (state : OverflowRegisters n) :
    (withOverflowBit bit).get state = bit.get state.1 := rfl

lemma ttkOverflowBit_get (n : Nat) (state : OverflowRegisters n) :
    (overflowBit n).get state = state.2 := rfl

lemma ttkWithOverflowBit_disjoint {n : Nat}
    (a b : EncodedBit (encoding n)) (hab : a.wire ≠ b.wire) :
    (withOverflowBit a).wire ≠ (withOverflowBit b).wire := by
  intro h
  apply hab
  apply Fin.ext
  have hval := congrArg (fun wire : Fin (overflowEncoding n).width => wire.val) h
  exact hval

lemma ttkWithOverflowBit_output_disjoint {n : Nat}
    (bit : EncodedBit (encoding n)) :
    (withOverflowBit bit).wire ≠ (overflowBit n).wire := by
  intro h
  have hval := congrArg Fin.val h
  change bit.wire.val = (encoding n).width at hval
  have hlt := bit.wire.isLt
  omega

/-- Lift one actual operand gate to the larger interface. -/
def withOverflowGate {n : Nat} :
    EncodedBit.GateSpec (encoding n) → EncodedBit.GateSpec (overflowEncoding n)
  | .x t => .x (withOverflowBit t)
  | .cnot c t h => .cnot (withOverflowBit c) (withOverflowBit t)
      (ttkWithOverflowBit_disjoint c t h)
  | .toffoli a b t hab hat hbt =>
      .toffoli (withOverflowBit a) (withOverflowBit b) (withOverflowBit t)
        (ttkWithOverflowBit_disjoint a b hab)
        (ttkWithOverflowBit_disjoint a t hat)
        (ttkWithOverflowBit_disjoint b t hbt)

/-- Lifting an operand gate preserves the explicit overflow output bit. -/
lemma ttkWithOverflowGate_step {n : Nat}
    (gate : EncodedBit.GateSpec (encoding n)) (state : OverflowRegisters n) :
    (withOverflowGate gate).step state = (gate.step state.1, state.2) := by
  cases gate with
  | x target => rfl
  | cnot control target hct =>
      change (if control.get state.1 then (target.flip state.1, state.2) else state) = _
      cases h : control.get state.1 <;> simp [EncodedBit.GateSpec.step,
        EncodedBit.cnotStep, h]
  | toffoli a b target hab hat hbt =>
      change (if a.get state.1 && b.get state.1 then
        (target.flip state.1, state.2) else state) = _
      cases h : a.get state.1 && b.get state.1 <;>
        simp [EncodedBit.GateSpec.step, EncodedBit.toffoliStep, h]

/-- The independent low-word addition specification. -/
def lowOutput {n : Nat} (state : Registers n) : Registers n :=
  (state.1, ⟨(state.1.val + state.2.val) % 2 ^ n,
    Nat.mod_lt _ (Nat.two_pow_pos n)⟩)

/-- The independent overflow specification accepts an arbitrary output bit. -/
def overflowOutput {n : Nat} (state : OverflowRegisters n) : OverflowRegisters n :=
  (lowOutput state.1, state.2 ^^ decide (2 ^ n ≤ state.1.1.val + state.1.2.val))

end

end QuantumAlg.MAU.Addition.TTK
