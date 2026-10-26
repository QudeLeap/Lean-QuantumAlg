/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Encoder.Height
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment.Metadata

/-! # Complete original-pool readouts after actual alignment and first-one encoding -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

/-- Mathematical intermediate of the two actual native preparation components. -/
def encodedState (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) : Data width :=
  GateSpec.stepList ((LengthEncoder.frame width field first).encoderGates
    (LengthEncoder.height width) (LengthEncoder.height_capacity width capacity)
    (LengthEncoder.height_fits width))
    (GateSpec.stepList (LengthAlignment.gates width field first) state)

/-- The complete original prefix returns zero after its full first-one traversal. -/
lemma encoded_prefix (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) :
    (encodedState width field first capacity state).2.2.1 = 0 := by
  have pool := LengthAlignment.gates_pool width field first state
  have clean : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.2.1 = 0 :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans prefixZero
  exact (LengthEncoder.prefix_read width field first (LengthEncoder.height width)
    (LengthEncoder.height_capacity width capacity)
    (LengthEncoder.height_fits width) _ clean).trans clean

/-- The full first-one computation retains the actual arbitrary original conjunction. -/
lemma encoded_conjunction (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) :
    (encodedState width field first capacity state).2.2.2 = state.2.2.2 := by
  have pool := LengthAlignment.gates_pool width field first state
  have clean : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.2.1 = 0 :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans prefixZero
  exact (LengthEncoder.conjunction_get width field first (LengthEncoder.height width)
    (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width) _ clean).trans
    (congrArg (fun value : Pool width => value.2.2) pool)

/-- Every original boundary bit is retained through alignment and complete first-one encoding. -/
lemma encoded_boundary (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) :
    boundaryValue field (encodedState width field first capacity state).1 =
      boundaryValue field state.1 := by
  have pool := LengthAlignment.gates_pool width field first state
  have clean : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.2.1 = 0 :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans prefixZero
  have retained : boundaryValue field (encodedState width field first capacity state).1 =
      boundaryValue field (GateSpec.stepList (LengthAlignment.gates width field first) state).1 :=
    by
    apply BitVec.eq_of_getMsbD_eq
    intro index within
    have read := LengthEncoder.source_get width field first (LengthEncoder.height width)
      (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width) _ clean
      (boundaryBit width field ⟨index, within⟩)
    simpa only [encodedState, sourceBit_get, boundaryBit_get] using read
  exact retained.trans (LengthAlignment.gates_boundary width field first state)

/-- Original Ctrl survives every emitted alignment, mask, child visit and restoration gate. -/
lemma encoded_control (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) :
    (encodedState width field first capacity state).1.control = state.1.control := by
  have pool := LengthAlignment.gates_pool width field first state
  have clean : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.2.1 = 0 :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans prefixZero
  exact (LengthEncoder.source_get width field first (LengthEncoder.height width)
    (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width) _ clean
    (SharedEEA.controlBit width)).trans
    (LengthAlignment.gates_control width field first state)

/-- A clean initial address stores the full original first position on enabled branches. -/
lemma encoded_address_toNat (width : Nat) (field : Field) (first : Bool)
    (capacity : width + 3 ≤ 2 ^ ScanMetadata.addressWidth width)
    (state : Data width) (prefixZero : state.2.2.1 = 0) (addressZero : state.2.1 = 0)
    (sentinelFits : width + 3 < 2 ^ ScanMetadata.addressWidth width) :
    (encodedState width field first capacity state).2.1.toNat =
      if state.1.control then NatFixedWidth.PriorityPrefix.firstOne
        (LengthAlignment.word width field first
          (GateSpec.stepList (LengthAlignment.gates width field first) state)) else 0 := by
  have pool := LengthAlignment.gates_pool width field first state
  have clean : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.2.1 = 0 :=
    (congrArg (fun value : Pool width => value.2.1) pool).trans prefixZero
  have address : (GateSpec.stepList (LengthAlignment.gates width field first) state).2.1 = 0 :=
    (congrArg (fun value : Pool width => value.1) pool).trans addressZero
  have read := LengthEncoder.address_read width field first (LengthEncoder.height width)
    (LengthEncoder.height_capacity width capacity) (LengthEncoder.height_fits width) _ clean
  rw [address] at read
  have reduced := read.trans BitVec.zero_xor
  simp only [LengthAlignment.gates_control] at reduced
  have naturalRead := congrArg BitVec.toNat reduced
  refine naturalRead.trans ?_
  have firstFits : NatFixedWidth.PriorityPrefix.firstOne
      (LengthAlignment.word width field first
        (GateSpec.stepList (LengthAlignment.gates width field first) state)) <
      2 ^ ScanMetadata.addressWidth width :=
    (Nat.sub_le (width + 3) _).trans_lt sentinelFits
  cases state.1.control
  · rfl
  · exact Nat.mod_eq_of_lt firstFits

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthPrepare
