/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Rows
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Retention
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Offset
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Complete original outside-wire retention by the actual streaming word

These laws require no helper or dirty initialization. They follow the same
literal native offset and increasing-index physical-reset rows on full encoded
labels, retaining every unaddressed physical system [G25, main.tex:209-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The actual original offset retains every original encoded wire outside the target ports. -/
lemma offsetGates_wire_read (layout : Layout encoding width) (constant : BitVec width)
    (observed : Fin encoding.width)
    (outside : ∀ index, (layout.target index).wire ≠ observed) (state : Data) :
    (encoding.encode (stepList (layout.offsetGates constant) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  apply stepList_preserves_of_targetFlipPreserves
    (project := fun current => (encoding.encode current).val.testBit
      (WireAddress.bitIndex observed).val) (layout.offsetGates constant)
  intro gate present
  rw [offsetGates_eq_controlledXor] at present
  unfold Word.controlledXorConstantGates at present
  obtain ⟨index, _present, rfl⟩ := List.mem_map.mp present
  change ∀ current,
    (encoding.encode ((layout.target index).flip current)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val
  intro current
  rw [(layout.target index).encode_flip, WireAddress.bit_flipBit_of_ne (outside index)]

/-- Every actual chronological prefix retains the complete original outside-wire readout. -/
lemma streamingRows_wire_read (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (observed : Fin encoding.width)
    (outside : ∀ port, (layout.bit port).wire ≠ observed)
    (state : Data) (count : Nat) (bounded : count ≤ width - 1) :
    (encoding.encode
      (wordLabel (layout.streamingRows wide constant count bounded) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  revert bounded
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bounded
      rw [streamingRows_label_succ, streamingStep_wire_read layout wide constant _ observed outside,
        ih (by omega)]

/-- The full actual streaming word retains every original system outside its declared ports. -/
lemma streamingWord_wire_read (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (observed : Fin encoding.width)
    (outside : ∀ port, (layout.bit port).wire ≠ observed) (state : Data) :
    (encoding.encode (wordLabel (layout.streamingWord wide constant) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  rw [streamingWord_eq_rows]
  change (encoding.encode (wordLabel (layout.streamingRows wide constant (width - 1) le_rfl)
    (stepList (layout.offsetGates constant) state))).val.testBit
      (WireAddress.bitIndex observed).val = _
  rw [streamingRows_wire_read layout wide constant observed outside,
    offsetGates_wire_read layout constant observed (fun index => outside (.inr (.inl index)))]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
