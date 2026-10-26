/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Template
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.StreamedSelector.SelectedPayload

/-!
# Actual selected-top signed overflow instructions

The top source position is the original full quantum address. One
ordinary native unary traversal performs the source overflow CNOT
before the descending xor stage; another performs the overflow carry
after the upward carry stage. Arbitrary original Iter supplies restored
dirty work for the latter's extra control
[TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop

noncomputable section

open EncodedBit WindowLookup StreamedSelector NumberTheory.SharedEEA

/-- The two overflow instructions keep their distinct source execution positions. -/
inductive Kind where
  | pre
  | carry

/-- Sign is the same original arbitrary overflow output, outside both operand words. -/
def sign (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (SharedEEA.signBit width)

private lemma word_sign_ne (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (ArithmeticTemplate.wordBit width first index).wire ≠ (sign width).wire := by
  intro same
  have values := congrArg Fin.val same
  change (ArithmeticTemplate.wordBit width first index).wire.val =
    (sourceBit width (SharedEEA.signBit width)).wire.val at values
  rw [ArithmeticTemplate.wordBit_value, sourceBit_wire, SharedEEA.signBit_wire] at values
  have within := index.isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] at values <;> omega

private def preGate (width : Nat) (index : Fin (width + 3)) : GateSpec (encoding width) :=
  .cnot (ArithmeticTemplate.wordBit width false index) (sign width)
    (word_sign_ne width false index)

private def carryGate (width : Nat) (index : Fin (width + 3)) : GateSpec (encoding width) :=
  .toffoli (ArithmeticTemplate.wordBit width true index)
    (ArithmeticTemplate.wordBit width false index) (sign width)
    (ArithmeticTemplate.word_ne width index index)
    (word_sign_ne width true index) (word_sign_ne width false index)

/-- Literal source native instructions, with the original width-one pre-overflow omission. -/
def source (width : Nat) (kind : Kind) (index : Nat) : List (GateSpec (encoding width)) :=
  if within : index < width + 3 then
    match kind with
    | .pre => if 0 < index then [preGate width ⟨index, within⟩] else []
    | .carry => [carryGate width ⟨index, within⟩]
  else []

private lemma word_below (width : Nat) (first : Bool) (index : Fin (width + 3)) :
    (ArithmeticTemplate.wordBit width first index).wire.val <
      (SharedEEA.iterationBit width).wire.val := by
  rw [ArithmeticTemplate.wordBit_value, SharedEEA.iterationBit_wire]
  have within := index.isLt
  cases first <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

private lemma sign_below (width : Nat) :
    (sign width).wire.val < (SharedEEA.iterationBit width).wire.val := by
  change (sourceBit width (SharedEEA.signBit width)).wire.val < _
  rw [sourceBit_wire, SharedEEA.signBit_wire, SharedEEA.iterationBit_wire]
  omega

private lemma source_below (width : Nat) (kind : Kind) (index : Nat)
    (gate : GateSpec (encoding width)) (present : gate ∈ source width kind index) :
    ArithmeticTemplate.below (SharedEEA.iterationBit width).wire.val gate := by
  by_cases within : index < width + 3
  · cases kind with
    | pre =>
        simp only [source, dif_pos within] at present
        split_ifs at present
        · simp only [List.mem_singleton] at present
          subst gate
          exact ⟨word_below width false _, sign_below width⟩
        · exact False.elim (List.not_mem_nil present)
    | carry =>
        simp only [source, dif_pos within, List.mem_singleton] at present
        subst gate
        exact ⟨word_below width true _, word_below width false _, sign_below width⟩
  · simp only [source, dif_neg within, List.not_mem_nil] at present

private lemma address_after (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (SharedEEA.iterationBit width).wire.val ≤
      ((SelectionFrame.frame width).address index).wire.val := by
  change (SharedEEA.iterationBit width).wire.val ≤ (addressBit width index).wire.val
  rw [SharedEEA.iterationBit_wire, addressBit_wire, SharedEEA.encoding_width]
  omega

private lemma stack_after (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1)) :
    (SharedEEA.iterationBit width).wire.val ≤
      ((SelectionFrame.frame width).stack index).wire.val := by
  change (SharedEEA.iterationBit width).wire.val ≤ (SelectionFrame.stack width index).wire.val
  unfold SelectionFrame.stack
  split
  · change (SharedEEA.iterationBit width).wire.val ≤
      (sourceBit width (SharedEEA.controlBit width)).wire.val
    rw [sourceBit_wire, SharedEEA.controlBit_wire, SharedEEA.iterationBit_wire]
    omega
  · rw [SharedEEA.iterationBit_wire, prefixBit_wire, SharedEEA.encoding_width]
    omega

/-- Complete frame certificates lower each literal top gate with the original arbitrary Iter. -/
def payload (width : Nat) (kind : Kind) (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    SelectedPayload (SelectionFrame.frame width) where
  source := source width kind label.val
  work := sourceBit width (SharedEEA.iterationBit width)
  sourceAddress := fun index gate present =>
    ArithmeticTemplate.below_disjoint gate (source_below width kind label.val gate present) _
      (address_after width index)
  sourceStack := fun index gate present =>
    ArithmeticTemplate.below_disjoint gate (source_below width kind label.val gate present) _
      (stack_after width index)
  workDisjoint := fun gate present =>
    ArithmeticTemplate.below_disjoint gate (source_below width kind label.val gate present) _
      (by rw [sourceBit_wire])
  controlWork := by
    change (SelectionFrame.stack width ⟨ScanMetadata.addressWidth width, by omega⟩).wire ≠ _
    unfold SelectionFrame.stack
    rw [dif_neg (by
      change ScanMetadata.addressWidth width ≠ 0
      unfold ScanMetadata.addressWidth
      omega)]
    exact (source_prefix_ne width _ _).symm

/-- The same original full address controls the actual native selected-top callback. -/
def callback (width : Nat) (kind : Kind)
    (label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (payload width kind label).program (QubitLayout.canonical _) .empty

/-- The actual tree retains precisely the original physical top positions. -/
def program (width : Nat) (kind : Kind) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (SelectionFrame.frame width).program (QubitLayout.canonical _) .empty
    (callback width kind) (SelectionScan.tree width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticTop
