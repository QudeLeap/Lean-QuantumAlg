/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Exponentiation.Gidney.Program
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Power.Oracle

/-!
# Literal reversible copy into an arbitrary exponentiation target

One CNOT per word bit XORs the computed power into a separate target word.
The target need not start at zero. The complete exponentiation state,
including its shared auxiliary word, is unchanged by this copy, so the
actual computation can then be reversed [VBE95, 9511018.tex:372-416].
-/

namespace QuantumAlg.MAU.Exponentiation.Gidney

noncomputable section

open BinaryLabelEncoding Nat.FixedWidth

/-- The exponentiation carrier and a separate arbitrary XOR target word. -/
abbrev OracleRegisters (exponentWidth width : Nat) :=
  Registers exponentWidth width × Fin (2 ^ width)

/-- The literal compute-copy-uncompute layout has only three width-qubit words. -/
def oracleEncoding (exponentWidth width : Nat) :
    BinaryLabelEncoding (OracleRegisters exponentWidth width) :=
  BinaryLabelEncoding.prod (encoding exponentWidth width) (finIdentity width)

private def powerWord (exponentWidth width : Nat) :
    EncodedBit.Word (encoding exponentWidth width) width where
  bit index := prodRightBit (finIdentity exponentWidth)
    (Multiplication.Accumulate.Gidney.encoding width)
    (prodLeftBit (finIdentity width) (finIdentity width)
      (finIdentityBit width (WireAddress.littleEndianWire index)))

private def sourceWord (exponentWidth width : Nat) :
    EncodedBit.Word (oracleEncoding exponentWidth width) width where
  bit index := prodLeftBit (encoding exponentWidth width) (finIdentity width)
    ((powerWord exponentWidth width).bit index)

private def targetWord (exponentWidth width : Nat) :
    EncodedBit.Word (oracleEncoding exponentWidth width) width where
  bit index := prodRightBit (encoding exponentWidth width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire index))

private theorem source_get (exponentWidth width : Nat) (index : Fin width)
    (state : OracleRegisters exponentWidth width) :
    ((sourceWord exponentWidth width).bit index).get state =
      state.1.2.1.val.testBit index.val := by
  change state.1.2.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem target_get (exponentWidth width : Nat) (index : Fin width)
    (state : OracleRegisters exponentWidth width) :
    ((targetWord exponentWidth width).bit index).get state = state.2.val.testBit index.val := by
  change state.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem source_target_disjoint (exponentWidth width : Nat)
    (source target : Fin width) :
    ((sourceWord exponentWidth width).bit source).wire ≠
      ((targetWord exponentWidth width).bit target).wire :=
  (EncodedBit.GateSpec.prodRightBit_wire_ne_prodLeftBit_wire
    (encoding exponentWidth width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire target))
    ((powerWord exponentWidth width).bit source)).symm

private theorem target_disjoint (exponentWidth width : Nat)
    (left right : Fin width) (distinct : left ≠ right) :
    ((targetWord exponentWidth width).bit left).wire ≠
      ((targetWord exponentWidth width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (encoding exponentWidth width).width + (width - 1 - left.val) =
    (encoding exponentWidth width).width + (width - 1 - right.val) at values
  apply distinct
  apply Fin.ext
  omega

/-- Exactly one real CNOT connects each computed bit to the corresponding target bit. -/
def copyGates (exponentWidth width : Nat) :
    List (EncodedBit.GateSpec (oracleEncoding exponentWidth width)) :=
  EncodedBit.Word.xorIntoGates (sourceWord exponentWidth width) (targetWord exponentWidth width)
    (fun index => source_target_disjoint exponentWidth width index index)

def copyProgram (exponentWidth width : Nat) :
    UnitaryCircuit (Qubits (oracleEncoding exponentWidth width).width) :=
  EncodedBit.GateSpec.programList (copyGates exponentWidth width)

private theorem copy_step (exponentWidth width : Nat)
    (state : OracleRegisters exponentWidth width) :
    EncodedBit.Word.xorIntoStep (sourceWord exponentWidth width) (targetWord exponentWidth width)
      (fun index => source_target_disjoint exponentWidth width index index) state =
        unitPowerCopyOutput state := by
  apply Prod.ext
  · exact EncodedBit.Word.xorIntoStep_preserves_projection
      (sourceWord exponentWidth width) (targetWord exponentWidth width)
      (fun index => source_target_disjoint exponentWidth width index index)
      Prod.fst (fun _ _ => rfl) state
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have actual := EncodedBit.Word.xorIntoStep_get_target
      (sourceWord exponentWidth width) (targetWord exponentWidth width)
      (fun index => source_target_disjoint exponentWidth width index index) index
      (fun other distinct => target_disjoint exponentWidth width other index distinct)
      (fun other => (source_target_disjoint exponentWidth width index other).symm) state
    have bits := Nat.testBit_xor state.2.val state.1.2.1.val index.val
    simp only [target_get, source_get] at actual
    exact actual.trans bits.symm

/-- Exact copy action holds for every initial target value and every compute-register label. -/
theorem gidneyExponentCopy_realizes (exponentWidth width : Nat) :
    UnitaryCircuit.Realizes (oracleEncoding exponentWidth width)
      (copyProgram exponentWidth width) unitPowerCopyOutput :=
  (EncodedBit.Word.xorInto_realizes
    (sourceWord exponentWidth width) (targetWord exponentWidth width)
    (fun index => source_target_disjoint exponentWidth width index index)).congrStep
      (copy_step exponentWidth width)

theorem gidneyExponentCopy_gate_count (exponentWidth width : Nat) :
    (copyGates exponentWidth width).length = width :=
  EncodedBit.Word.xorIntoGates_length
    (sourceWord exponentWidth width) (targetWord exponentWidth width)
    (fun index => source_target_disjoint exponentWidth width index index)

/-- The native ledger consists of precisely width uncontrolled CNOT occurrences. -/
theorem gidneyExponentCopy_eventCost (exponentWidth width : Nat) :
    (copyProgram exponentWidth width).eventCost =
      ResourcePool.ofList (List.replicate width (.gate (.builtin "cnot"))) := by
  rw [copyProgram, EncodedBit.GateSpec.programList_eventCost]
  unfold copyGates EncodedBit.Word.xorIntoGates
  rw [List.map_ofFn]
  change ResourcePool.ofList
    (List.ofFn fun _ : Fin width => Resource.Event.gate (.builtin "cnot")) = _
  rw [List.ofFn_const]

theorem gidneyExponentCopy_serial_resources (exponentWidth width : Nat) :
    (copyProgram exponentWidth width).eventCost.card = width ∧
      (copyProgram exponentWidth width).evaluatedEventDepth (fun _ => 1) = width := by
  constructor
  · exact (EncodedBit.GateSpec.programList_eventCost_card (copyGates exponentWidth width)).trans
      (gidneyExponentCopy_gate_count exponentWidth width)
  · exact (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
      (copyGates exponentWidth width)).trans (gidneyExponentCopy_gate_count exponentWidth width)

theorem gidneyExponentCopy_physical_range (exponentWidth width : Nat) :
    (copyProgram exponentWidth width).physical_idx ⊆ List.range (exponentWidth + 3 * width) := by
  have actual := EncodedBit.GateSpec.programList_physical_idx_subset_range
    (copyGates exponentWidth width)
  have size : (oracleEncoding exponentWidth width).width = exponentWidth + 3 * width := by
    change (exponentWidth + (width + width)) + width = exponentWidth + 3 * width
    omega
  simpa only [size, copyProgram] using actual

end

end QuantumAlg.MAU.Exponentiation.Gidney
