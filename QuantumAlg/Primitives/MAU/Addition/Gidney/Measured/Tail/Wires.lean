/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Tail.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Wires
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout

/-!
# Full original outside-wire retention of the complete actual measured adder

The actual stream, both native complements and the native dirty-carry repair
retain every unaddressed encoded system. This includes arbitrary dirty data
and any surrounding register alongside the external reference
[G25, main.tex:209-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec Instruction

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The literal native target complement retains every other original encoded wire. -/
lemma complementGates_wire_read (layout : Layout encoding width)
    (observed : Fin encoding.width)
    (outside : ∀ index, (layout.target index).wire ≠ observed) (state : Data) :
    (encoding.encode (stepList layout.complementGates state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  apply stepList_preserves_of_targetFlipPreserves
    (project := fun current => (encoding.encode current).val.testBit
      (WireAddress.bitIndex observed).val) layout.complementGates
  intro gate present
  unfold complementGates at present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
  change ∀ current,
    (encoding.encode ((layout.target index).flip current)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val
  intro current
  rw [(layout.target index).encode_flip, WireAddress.bit_flipBit_of_ne (outside index)]

/-- The complete actual measured word retains every system outside its declared physical ports. -/
lemma adderWord_wire_read (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (observed : Fin encoding.width)
    (outside : ∀ port, (layout.bit port).wire ≠ observed) (state : Data) :
    (encoding.encode (wordLabel (layout.adderWord wide constant) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val := by
  rw [adderWord_label, complementGates_wire_read layout observed
    (fun index => outside (.inr (.inl index))),
    CarryLayout.gates_wire_read layout.carryLayout _ observed
      (fun index => outside (.inr (.inr (.inl index)))),
    complementedStream, complementGates_wire_read layout observed
      (fun index => outside (.inr (.inl index))),
    streamingWord_wire_read layout wide constant observed outside]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
