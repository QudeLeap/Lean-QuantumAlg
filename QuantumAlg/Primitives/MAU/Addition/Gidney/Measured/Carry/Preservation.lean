/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Step

/-!
# Complete source and control retention by the actual carry word

Native affine-control conjugations restore their temporary source writes.
The recursive word therefore preserves every projection unchanged by flipping
its carry outputs, including arbitrary untouched original encoded wires.
No dirty-output initialization is required [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

lemma descendingTop_preserves {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) {Value : Type} (project : Data → Value)
    (untouched : ∀ state, project ((layout.output (Fin.last length)).flip state) = project state)
    (state : Data) :
    project (stepList (layout.descendingTop constant positive) state) = project state := by
  rw [descendingTop_step]
  split_ifs
  · exact untouched state
  · rfl

lemma ascendingTop_preserves {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) {Value : Type} (project : Data → Value)
    (untouched : ∀ state, project ((layout.output (Fin.last length)).flip state) = project state)
    (state : Data) :
    project (stepList (layout.ascendingTop constant positive) state) = project state := by
  rw [ascendingTop_step]
  split_ifs
  · exact untouched state
  · rfl

lemma topOffsetGates_preserves {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    {Value : Type} (project : Data → Value)
    (untouched : ∀ state, project ((layout.output (Fin.last length)).flip state) = project state)
    (state : Data) :
    project (stepList (layout.topOffsetGates constant) state) = project state := by
  unfold topOffsetGates
  split_ifs
  · change project (cnotStep layout.control (layout.output (Fin.last length)) state) = _
    unfold cnotStep
    split_ifs
    · exact untouched state
    · rfl
  · rfl

/-- The actual full native word preserves every property insensitive to its output flips. -/
lemma gates_preserves {Value : Type} (project : Data → Value) :
    ∀ {length : Nat} (layout : CarryLayout encoding length) (constant : BitVec length),
    (∀ index state, project ((layout.output index).flip state) = project state) →
      ∀ state, project (stepList (layout.gates constant) state) = project state := by
  intro length
  induction length with
  | zero => intro layout constant untouched state; rfl
  | succ length ih =>
      intro layout constant untouched state
      by_cases positive : 0 < length
      · rw [gates, dif_pos positive]
        simp only [stepList_append]
        rw [ascendingTop_preserves layout constant positive project (untouched _),
          topOffsetGates_preserves layout constant project (untouched _),
          ih layout.lower (constant.setWidth length)
            (fun index => untouched index.castSucc),
          descendingTop_preserves layout constant positive project (untouched _)]
      · have zero : length = 0 := by omega
        subst length
        rw [gates, dif_neg (by omega : ¬ 0 < 0), lowWord_step]
        split_ifs
        · exact untouched _ state
        · rfl

/-- The exact actual carry word retains the original coherent quantum-control label. -/
lemma gates_control_get {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (state : Data) :
    layout.control.get (stepList (layout.gates constant) state) = layout.control.get state :=
  gates_preserves layout.control.get layout constant
    (fun index => get_flip_of_wire_ne (layout.output index) layout.control
      (layout.control_output_ne index).symm) state

/-- Every original source bit remains unchanged, including its correlations with all outputs. -/
lemma gates_source_get {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (index : Fin length) (state : Data) :
    (layout.source index).get (stepList (layout.gates constant) state) =
      (layout.source index).get state :=
  gates_preserves (layout.source index).get layout constant
    (fun output => get_flip_of_wire_ne (layout.output output) (layout.source index)
      (layout.source_output_ne index output).symm) state

/-- Every other original physical encoded wire is retained, with no value restriction. -/
lemma gates_wire_read {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (observed : Fin encoding.width)
    (outside : ∀ index, (layout.output index).wire ≠ observed) (state : Data) :
    (encoding.encode (stepList (layout.gates constant) state)).val.testBit
        (WireAddress.bitIndex observed).val =
      (encoding.encode state).val.testBit (WireAddress.bitIndex observed).val :=
  gates_preserves (fun current =>
    (encoding.encode current).val.testBit (WireAddress.bitIndex observed).val) layout constant
    (fun index current => by
      rw [(layout.output index).encode_flip, WireAddress.bit_flipBit_of_ne (outside index)]) state

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
