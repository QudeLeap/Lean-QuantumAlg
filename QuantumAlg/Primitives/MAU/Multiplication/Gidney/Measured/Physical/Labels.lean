/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Layout.Readout
import all QuantumAlg.Util.Nat.FixedWidth
import Batteries.Data.BitVec.Lemmas

/-!
# Actual complete physical labels for the measured arithmetic frame

Every port value is placed at its original explicit physical address. The
decoder below is the real big-endian computational decoder, including both
arithmetic words, the two helpers and the flag [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical

noncomputable section

/-- Construct the actual computational label from all original addressed port values. -/
def label (width : Nat) (values : Port width → Bool) : Registers width :=
  (BitVec.ofFnLE fun index : Fin (2 * width + 4) =>
    values ((ports width).symm (WireAddress.littleEndianWire index))).toFin

/-- Every complete original bit lens reads exactly the value placed at its physical address. -/
lemma label_bit (width : Nat) (values : Port width → Bool) (port : Port width) :
    ((layout width).bit port).get (label width values) = values port := by
  change (BitVec.ofFnLE fun index : Fin (2 * width + 4) =>
    values ((ports width).symm (WireAddress.littleEndianWire index))).toNat.testBit
      (WireAddress.bitIndex (ports width port)).val = values port
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofFnLE,
    dif_pos (WireAddress.bitIndex (ports width port)).isLt]
  change values ((ports width).symm
    (WireAddress.littleEndianWire (WireAddress.bitIndex (ports width port)))) = values port
  rw [WireAddress.littleEndianWire_bitIndex, Equiv.symm_apply_apply]

/-- All original port readouts determine the complete physical label, with no missing wires. -/
lemma label_ext (width : Nat) (first second : Registers width)
    (same : ∀ port, ((layout width).bit port).get first = ((layout width).bit port).get second) :
    first = second := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  let port := (ports width).symm (WireAddress.littleEndianWire index)
  have actual := same port
  change first.val.testBit (WireAddress.bitIndex (ports width port)).val =
    second.val.testBit (WireAddress.bitIndex (ports width port)).val at actual
  simpa only [port, Equiv.apply_symm_apply, WireAddress.bitIndex_littleEndianWire] using actual

/-- The physically complete port assignment is injectively represented by computational labels. -/
lemma label_injective (width : Nat) : Function.Injective (label width) := by
  intro first second same
  funext port
  have read := congrArg (((layout width).bit port).get) same
  rwa [label_bit, label_bit] at read

/-- Canonical stage input retains its source and clears the auxiliary and three helpers. -/
def cleanLabel (width : Nat) (control : Bool) (source : BitVec width) : Registers width :=
  label width fun port =>
    match port with
    | .inl () => control
    | .inr (.inl index) => source.getLsbD index.val
    | .inr (.inr _) => false

/-- The actual stage control is the original coherent Boolean value. -/
lemma cleanLabel_control (width : Nat) (control : Bool) (source : BitVec width) :
    (layout width).control.get (cleanLabel width control source) = control :=
  label_bit width _ (.inl ())

/-- The actual source word decodes the original full-width little-endian arithmetic value. -/
lemma cleanLabel_source (width : Nat) (control : Bool) (source : BitVec width) :
    (layout width).sourceWord (cleanLabel width control source) = source := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  change ((layout width).sourceWord (cleanLabel width control source)).toNat.testBit index = _
  rw [Layout.multiplicationSourceWord_bit _ _ _ inside]
  exact label_bit width _ (.inr (.inl ⟨index, inside⟩))

/-- The original target accumulator is physically zero at the stage input. -/
lemma cleanLabel_target (width : Nat) (control : Bool) (source : BitVec width) :
    (layout width).targetWord (cleanLabel width control source) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro index inside
  change ((layout width).targetWord (cleanLabel width control source)).toNat.testBit index = _
  rw [Layout.multiplicationTargetWord_bit _ _ _ inside]
  have actual : ((layout width).target ⟨index, inside⟩).get
      (cleanLabel width control source) = false :=
    label_bit width _ (.inr (.inr (.inl ⟨index, inside⟩)))
  simpa using actual

/-- Both actual helpers and the actual reduction flag are zero in the canonical stage input. -/
lemma cleanLabel_helpers (width : Nat) (control : Bool) (source : BitVec width) :
    (∀ helper, ((layout width).clean helper).get (cleanLabel width control source) = false) ∧
      (layout width).flag.get (cleanLabel width control source) = false := by
  constructor
  · intro helper
    exact label_bit width _ (.inr (.inr (.inr (.inl helper))))
  · exact label_bit width _ (.inr (.inr (.inr (.inr ()))))

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured.Physical
