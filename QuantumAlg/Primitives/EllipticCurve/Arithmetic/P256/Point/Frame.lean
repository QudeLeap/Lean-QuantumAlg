/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Copy
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Total

/-!
# Complete original three-word point frame and the three point suffix wires

The original scanned source, including every padding and history bit and
the complete 21-bit pool, precedes the original arbitrary numerator word.
The suffix contains the supplied point control C, the normal selector N,
and the clean arithmetic/fusion work W, in that order. W is workspace,
not an additional external algorithm control. Existing window controls
can subsequently be retained as an identity suffix.

The three arithmetic flags are borrowed from actual initialized pool
positions. Their cleanliness is a caller obligation at the arithmetic
boundary; this static frame does not assert that an EEA call occurred.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Frame

noncomputable section

open BinaryLabelEncoding

/-- C, N and W, all physically separate from the original inversion frame. -/
abbrev Controls := Bool × (Bool × Bool)

def controlsEncoding : BinaryLabelEncoding Controls := .prod .bool (.prod .bool .bool)

@[implicit_reducible]
private def payloadWidth : Nat := 256

/-- Three original 256-bit payloads, the complete original history/pool, and C/N/W. -/
abbrev Raw := MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data payloadWidth × Controls

private def encodingAt (width : Nat) : BinaryLabelEncoding
    (MAU.Inversion.SharedEEA.Scanned.OutputCopy.Data width × Controls) :=
  .prod (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding width) controlsEncoding

def encoding : BinaryLabelEncoding Raw := encodingAt payloadWidth

lemma encoding_width : encoding.width = 839 := by
  change (MAU.Inversion.SharedEEA.Scanned.encoding 256).width + 256 + (1 + (1 + 1)) = 839
  rw [MAU.Inversion.SharedEEA.Scanned.p256_encoding_width]

private lemma product_total {Left Right : Type}
    (left : BinaryLabelEncoding Left) (right : BinaryLabelEncoding Right)
    (leftOnto : Function.Surjective left.encode)
    (rightOnto : Function.Surjective right.encode) :
    Function.Surjective (BinaryLabelEncoding.prod left right).encode := by
  intro label
  obtain ⟨⟨first, second⟩, rfl⟩ :=
    (prodEquiv (m := left.width) (n := right.width)).surjective label
  obtain ⟨leftValue, rfl⟩ := leftOnto first
  obtain ⟨rightValue, rfl⟩ := rightOnto second
  exact ⟨(leftValue, rightValue), rfl⟩

private lemma bool_total : Function.Surjective BinaryLabelEncoding.bool.encode := by
  intro label
  obtain ⟨value, rfl⟩ := finTwoEquiv.symm.surjective label
  refine ⟨value, ?_⟩
  cases value <;> rfl

private lemma encodingAt_total (width : Nat) : Function.Surjective (encodingAt width).encode :=
  product_total _ _
    (product_total _ _ (MAU.Inversion.SharedEEA.Scanned.encoding_surjective width)
      (fun label => ⟨label, rfl⟩))
    (product_total _ _ bool_total (product_total _ _ bool_total bool_total))

section

attribute [local irreducible] payloadWidth

/-- The complete physical frame covers every binary label, including arbitrary history and pool. -/
lemma encoding_surjective : Function.Surjective encoding.encode := encodingAt_total payloadWidth

end

/-- Keep an original scan coordinate at exactly its original physical identity. -/
def scanBit (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256)) :
    EncodedBit encoding :=
  prodLeftBit (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256) controlsEncoding
    (prodLeftBit (MAU.Inversion.SharedEEA.Scanned.encoding 256) (finIdentity 256) bit)

lemma scanBit_wire (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256)) :
    (scanBit bit).wire.val = bit.wire.val := rfl

lemma scanBit_get (bit : EncodedBit (MAU.Inversion.SharedEEA.Scanned.encoding 256))
    (state : Raw) : (scanBit bit).get state = bit.get state.1.1 := rfl

/-- Original Work1 numerical bit i occupies original physical position i. -/
def work1Bit (index : Fin 256) : EncodedBit encoding :=
  scanBit (MAU.Inversion.SharedEEA.Scanned.sourceBit 256
    (MAU.Inversion.SharedEEA.firstWordBit 256 ⟨index.val, by omega⟩))

/-- Original Work2 numerical bit i occupies original physical position 259+i. -/
def work2Bit (index : Fin 256) : EncodedBit encoding :=
  scanBit (MAU.Inversion.SharedEEA.Scanned.sourceBit 256
    (MAU.Inversion.SharedEEA.secondWordBit 256 ⟨index.val, by omega⟩))

/-- The original separate numerator keeps its original finite-word bit order. -/
def numeratorBit (index : Fin 256) : EncodedBit encoding :=
  prodLeftBit (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256) controlsEncoding
    (prodRightBit (MAU.Inversion.SharedEEA.Scanned.encoding 256) (finIdentity 256)
      (finIdentityBit 256 (WireAddress.littleEndianWire index)))

lemma work1Bit_wire (index : Fin 256) : (work1Bit index).wire.val = index.val := rfl

lemma work2Bit_wire (index : Fin 256) : (work2Bit index).wire.val = 259 + index.val := rfl

lemma numeratorBit_wire (index : Fin 256) :
    (numeratorBit index).wire.val = 580 + (255 - index.val) := by
  change (MAU.Inversion.SharedEEA.Scanned.encoding 256).width + (256 - 1 - index.val) = _
  rw [MAU.Inversion.SharedEEA.Scanned.p256_encoding_width]

/-- Numerical Work1 payload; its other three physical wires remain present in Raw. -/
def work1 (state : Raw) : Fin (2 ^ 256) :=
  BitVec.equivFin (state.1.1.1.firstWord.reverse.setWidth 256)

def work2 (state : Raw) : Fin (2 ^ 256) :=
  MAU.Inversion.SharedEEA.OutputCopy.value state.1.1.1

def numerator (state : Raw) : Fin (2 ^ 256) := state.1.2

lemma work1Bit_get (index : Fin 256) (state : Raw) :
    (work1Bit index).get state = (work1 state).val.testBit index.val := by
  change (MAU.Inversion.SharedEEA.firstWordBit 256 ⟨index.val, by omega⟩).get state.1.1.1 =
    (state.1.1.1.firstWord.reverse.setWidth 256).getLsbD index.val
  rw [MAU.Inversion.SharedEEA.firstWordBit_get,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and]

lemma work2Bit_get (index : Fin 256) (state : Raw) :
    (work2Bit index).get state = (work2 state).val.testBit index.val := by
  change (MAU.Inversion.SharedEEA.secondWordBit 256 ⟨index.val, by omega⟩).get state.1.1.1 =
    (state.1.1.1.secondWord.reverse.setWidth 256).getLsbD index.val
  rw [MAU.Inversion.SharedEEA.secondWordBit_get,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and]

lemma numeratorBit_get (index : Fin 256) (state : Raw) :
    (numeratorBit index).get state = (numerator state).val.testBit index.val := by
  change state.1.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]
  rfl

def pointControlBit : EncodedBit encoding :=
  prodRightBit (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256) controlsEncoding
    (prodLeftBit .bool (.prod .bool .bool) boolBit)

def normalBit : EncodedBit encoding :=
  prodRightBit (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256) controlsEncoding
    (prodRightBit .bool (.prod .bool .bool) (prodLeftBit .bool .bool boolBit))

def workBit : EncodedBit encoding :=
  prodRightBit (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256) controlsEncoding
    (prodRightBit .bool (.prod .bool .bool) (prodRightBit .bool .bool boolBit))

private lemma original_width :
    (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256).width = 836 := by
  change (MAU.Inversion.SharedEEA.Scanned.encoding 256).width + 256 = 836
  rw [MAU.Inversion.SharedEEA.Scanned.p256_encoding_width]

lemma pointControlBit_wire : pointControlBit.wire.val = 836 := original_width

lemma normalBit_wire : normalBit.wire.val = 837 := by
  change (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256).width + (1 + 0) = 837
  rw [original_width]

lemma workBit_wire : workBit.wire.val = 838 := by
  change (MAU.Inversion.SharedEEA.Scanned.OutputCopy.encoding 256).width + (1 + (1 + 0)) = 838
  rw [original_width]

lemma pointControlBit_get (state : Raw) : pointControlBit.get state = state.2.1 := rfl

lemma normalBit_get (state : Raw) : normalBit.get state = state.2.2.1 := rfl

lemma workBit_get (state : Raw) : workBit.get state = state.2.2.2 := rfl

/-- Reduction borrows original address bit zero; no resident flag is added. -/
def reductionBit : EncodedBit encoding :=
  scanBit (MAU.Inversion.SharedEEA.Scanned.addressBit 256 ⟨0, by decide⟩)

/-- The multiplier/control latch borrows original prefix bit zero. -/
def latchBit : EncodedBit encoding :=
  scanBit (MAU.Inversion.SharedEEA.Scanned.prefixBit 256 ⟨0, by decide⟩)

/-- The selected native lowering borrows the original conjunction bit. -/
def loweringBit : EncodedBit encoding :=
  scanBit (MAU.Inversion.SharedEEA.Scanned.conjunctionBit 256)

lemma reductionBit_wire : reductionBit.wire.val = 559 := by
  change (MAU.Inversion.SharedEEA.encoding 256).width + 0 = 559
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

lemma latchBit_wire : latchBit.wire.val = 569 := by
  change (MAU.Inversion.SharedEEA.encoding 256).width +
    (NumberTheory.SharedEEA.ScanMetadata.addressWidth 256 + 0) = 569
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

lemma loweringBit_wire : loweringBit.wire.val = 579 := by
  change (MAU.Inversion.SharedEEA.encoding 256).width +
    (NumberTheory.SharedEEA.ScanMetadata.addressWidth 256 +
      (NumberTheory.SharedEEA.ScanMetadata.addressWidth 256 + 0)) = 579
  rw [MAU.Inversion.SharedEEA.encoding_width]
  decide

/-- Exactly the initialized caller-owned scan pool at an arithmetic boundary. -/
def CleanPool (state : Raw) : Prop := state.1.1.2 = (0, (0, false))

lemma arithmetic_flags_clean (state : Raw) (clean : CleanPool state) :
    reductionBit.get state = false ∧ latchBit.get state = false ∧
      loweringBit.get state = false := by
  change state.1.1.2.1.getMsbD 0 = false ∧ state.1.1.2.2.1.getMsbD 0 = false ∧
    state.1.1.2.2.2 = false
  rw [show state.1.1.2 = (0, (0, false)) from clean]
  decide

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Frame
