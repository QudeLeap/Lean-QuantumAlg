/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.QubitPrimitive
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Literal CNOT copy from the physical shared-EEA output coefficient

The corrected coefficient occupies the first Work2 wires in physical
little-endian order. One actual CNOT per output bit XORs those wires into
a separate n-bit word. The complete forward frame, including every bit
of Gamma, remains unchanged and can subsequently be reversed
[LYL+26, sec_EEA/sub_4phase.tex:105,123-128].

The target may contain any initial value. Outside the reached input
domain the same native program copies the low n numerical coefficient
bits; no fit, zero target, or clean borrowed-frame hypothesis is needed
for its full-label unitary action.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.OutputCopy

noncomputable section

open BinaryLabelEncoding

/-- The complete retained forward frame and a separate arbitrary n-bit XOR output. -/
abbrev Data (width : Nat) := Registers width × Fin (2 ^ width)

/-- All source fields remain live beside the actual output word. -/
def encoding (width : Nat) : BinaryLabelEncoding (Data width) :=
  BinaryLabelEncoding.prod (SharedEEA.encoding width) (finIdentity width)

private def sourceIndex (width : Nat) (index : Fin width) : Fin (width + 3) :=
  ⟨index.val, by omega⟩

private def sourceWord (width : Nat) : EncodedBit.Word (encoding width) width where
  bit index := prodLeftBit (SharedEEA.encoding width) (finIdentity width)
    (secondWordBit width (sourceIndex width index))

private def targetWord (width : Nat) : EncodedBit.Word (encoding width) width where
  bit index := prodRightBit (SharedEEA.encoding width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire index))

/-- The actual n copied numerical bits, defined for every original frame. -/
def value {width : Nat} (state : Registers width) : Fin (2 ^ width) :=
  BitVec.equivFin (state.secondWord.reverse.setWidth width)

private theorem source_get (width : Nat) (index : Fin width) (state : Data width) :
    ((sourceWord width).bit index).get state = (value state.1).val.testBit index.val := by
  change (secondWordBit width (sourceIndex width index)).get state.1 =
    (state.1.secondWord.reverse.setWidth width).getLsbD index.val
  rw [secondWordBit_get, BitVec.getLsbD_setWidth, BitVec.getLsbD_reverse]
  simp only [index.isLt, decide_true, Bool.true_and]
  rfl

private theorem target_get (width : Nat) (index : Fin width) (state : Data width) :
    ((targetWord width).bit index).get state = state.2.val.testBit index.val := by
  change state.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem source_target_disjoint (width : Nat) (source target : Fin width) :
    ((sourceWord width).bit source).wire ≠ ((targetWord width).bit target).wire :=
  (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (SharedEEA.encoding width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire target))
    (secondWordBit width (sourceIndex width source))).symm

private theorem target_disjoint (width : Nat) (left right : Fin width)
    (distinct : left ≠ right) :
    ((targetWord width).bit left).wire ≠ ((targetWord width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (SharedEEA.encoding width).width + (width - 1 - left.val) =
    (SharedEEA.encoding width).width + (width - 1 - right.val) at values
  apply distinct
  apply Fin.ext
  omega

/-- The literal original-wire CNOT list, including the width-zero list. -/
def gates (width : Nat) : List (EncodedBit.GateSpec (encoding width)) :=
  EncodedBit.Word.xorIntoGates (sourceWord width) (targetWord width)
    (fun index => source_target_disjoint width index index)

/-- Execute those same n actual CNOT occurrences. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  EncodedBit.GateSpec.programList (gates width)

/-- The complete retained frame is unchanged and only the arbitrary output is xored. -/
def step {width : Nat} (state : Data width) : Data width :=
  (state.1, ⟨state.2.val ^^^ (value state.1).val,
    Nat.xor_lt_two_pow state.2.isLt (value state.1).isLt⟩)

private theorem gates_step (width : Nat) (state : Data width) :
    EncodedBit.Word.xorIntoStep (sourceWord width) (targetWord width)
      (fun index => source_target_disjoint width index index) state = step state := by
  apply Prod.ext
  · exact EncodedBit.Word.xorIntoStep_preserves_projection
      (sourceWord width) (targetWord width)
      (fun index => source_target_disjoint width index index)
      Prod.fst (fun _ _ => rfl) state
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have actual := EncodedBit.Word.xorIntoStep_get_target
      (sourceWord width) (targetWord width)
      (fun index => source_target_disjoint width index index) index
      (fun other distinct => target_disjoint width other index distinct)
      (fun other => (source_target_disjoint width index other).symm) state
    simp only [target_get, source_get] at actual
    exact actual.trans (Nat.testBit_xor state.2.val (value state.1).val index.val).symm

/-- Exact native action preserves every compute-state correlation and arbitrary target value. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  (EncodedBit.Word.xorInto_realizes (sourceWord width) (targetWord width)
    (fun index => source_target_disjoint width index index)).congrStep (gates_step width)

/-- An internally proved fitted coefficient is copied completely without truncation. -/
theorem value_of_fits {width : Nat} (state : Registers width)
    (fits : state.secondWord.reverse.toNat < 2 ^ width) :
    (value state).val = state.secondWord.reverse.toNat := by
  change (state.secondWord.reverse.setWidth width).toNat = _
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt fits]

/-- The actual copy leaves the entire input frame available to the same computation's dagger. -/
theorem step_frame (width : Nat) (state : Data width) : (step state).1 = state.1 := rfl

/-- The actual event list contains exactly one CNOT for each output position. -/
theorem gates_length (width : Nat) : (gates width).length = width :=
  EncodedBit.Word.xorIntoGates_length (sourceWord width) (targetWord width)
    (fun index => source_target_disjoint width index index)

/-- Literal native coordinates are n uncontrolled CNOT occurrences. -/
theorem program_eventCost (width : Nat) :
    (program width).eventCost =
      ResourcePool.ofList (List.replicate width (.gate (.builtin "cnot"))) := by
  rw [program, EncodedBit.GateSpec.programList_eventCost]
  unfold gates EncodedBit.Word.xorIntoGates
  rw [List.map_ofFn]
  change ResourcePool.ofList
    (List.ofFn fun _ : Fin width => Resource.Event.gate (.builtin "cnot")) = _
  rw [List.ofFn_const]

/-- Literal list scheduling charges each of those same actual CNOT occurrences. -/
theorem program_serial_resources (width : Nat) :
    (program width).eventCost.card = width ∧
      (program width).evaluatedEventDepth (fun _ => 1) = width := by
  constructor
  · exact (EncodedBit.GateSpec.programList_eventCost_card (gates width)).trans (gates_length width)
  · exact (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
      (gates width)).trans (gates_length width)

/-- Every actual copy address lies in the original frame plus the declared output word. -/
theorem program_physical_range (width : Nat) :
    (program width).physical_idx ⊆ List.range (encoding width).width :=
  EncodedBit.GateSpec.programList_physical_idx_subset_range (gates width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.OutputCopy
