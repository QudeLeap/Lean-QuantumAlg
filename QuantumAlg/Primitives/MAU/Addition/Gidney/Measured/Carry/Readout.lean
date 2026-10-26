/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Step

/-!
# Original dirty-output readouts of the actual native carry rows

These equations project the exact full-label native step laws. The original
dirty bit remains explicit in every xor, so the cancellation invariant does
not assume that any dirty output is initialized [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma read_conditional_flip (target : EncodedBit encoding) (active : Bool) (state : Data) :
    target.get (if active then target.flip state else state) = (target.get state ^^ active) := by
  cases active <;> simp [get_flip_self]

/-- The descending native row records the contribution of the original dirty predecessor. -/
lemma descendingTop_get_output {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) (state : Data) :
    let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
    let top : Fin (length + 1) := Fin.last length
    (layout.output top).get (stepList (layout.descendingTop constant positive) state) =
      ((layout.output top).get state ^^
        (((layout.source top).get state ^^
          (constant.getLsbD length && layout.control.get state)) &&
            (layout.output previous).get state)) := by
  dsimp only
  rw [descendingTop_step, read_conditional_flip]

/-- The ascending native row reads the updated predecessor with the same affine offset. -/
lemma ascendingTop_get_output {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) (state : Data) :
    let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
    let top : Fin (length + 1) := Fin.last length
    (layout.output top).get (stepList (layout.ascendingTop constant positive) state) =
      ((layout.output top).get state ^^
        (((layout.source top).get state ^^
          (constant.getLsbD length && layout.control.get state)) &&
            ((layout.output previous).get state ^^
              (constant.getLsbD length && layout.control.get state)))) := by
  dsimp only
  rw [ascendingTop_step, read_conditional_flip]

/-- The independent actual row CNOT contributes exactly its selected quantum-offset bit. -/
lemma topOffsetGates_get_output {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (state : Data) :
    (layout.output (Fin.last length)).get (stepList (layout.topOffsetGates constant) state) =
      ((layout.output (Fin.last length)).get state ^^
        (constant.getLsbD length && layout.control.get state)) := by
  unfold topOffsetGates
  cases constant.getLsbD length <;>
    simp [stepList, step, cnotStep_get_target]

/-- The actual low row xors the first carry while retaining its arbitrary dirty input. -/
lemma lowWord_get_output (layout : CarryLayout encoding 1) (constant : BitVec 1) (state : Data) :
    (layout.output 0).get
        (stepList (layout.topOffsetGates constant ++ layout.lowGates constant) state) =
      ((layout.output 0).get state ^^
        ((layout.source 0).get state && (constant.getLsbD 0 && layout.control.get state))) := by
  rw [lowWord_step, read_conditional_flip]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
