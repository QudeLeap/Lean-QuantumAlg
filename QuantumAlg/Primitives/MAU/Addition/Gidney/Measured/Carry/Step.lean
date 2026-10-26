/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates

/-!
# Exact full-label action of the actual native carry rows

Each row word modifies only its named carry output. In particular its source
and quantum-control values are restored exactly. The dirty predecessor remains
arbitrary in both affine-control words [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The descending row is exactly one xor into its top dirty bit on every complete input label. -/
lemma descendingTop_step {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) (state : Data) :
    let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
    let top : Fin (length + 1) := Fin.last length
    stepList (layout.descendingTop constant positive) state =
      if ((layout.source top).get state ^^ (constant.getLsbD length && layout.control.get state)) &&
          (layout.output previous).get state then (layout.output top).flip state else state := by
  dsimp only
  unfold descendingTop
  rw [affineToffoliGates_step
    (offsetOutput := layout.control_output_ne (Fin.last length))]
  simp only [Bool.false_and, Bool.xor_false, Fin.val_last]

/-- The ascending row reads the updated predecessor with the same selected offset xor. -/
lemma ascendingTop_step {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) (state : Data) :
    let previous : Fin (length + 1) := ⟨length - 1, by omega⟩
    let top : Fin (length + 1) := Fin.last length
    stepList (layout.ascendingTop constant positive) state =
      if ((layout.source top).get state ^^ (constant.getLsbD length && layout.control.get state)) &&
          ((layout.output previous).get state ^^
            (constant.getLsbD length && layout.control.get state)) then
        (layout.output top).flip state else state := by
  dsimp only
  unfold ascendingTop
  rw [affineToffoliGates_step
    (offsetOutput := layout.control_output_ne (Fin.last length))]
  simp only [Fin.val_last]

/-- The actual low row leaves the arbitrary dirty input xored with its zero-input carry. -/
lemma lowWord_step (layout : CarryLayout encoding 1) (constant : BitVec 1) (state : Data) :
    stepList (layout.topOffsetGates constant ++ layout.lowGates constant) state =
      if (layout.source 0).get state && (constant.getLsbD 0 && layout.control.get state) then
        (layout.output 0).flip state else state := by
  have controlAtSource := get_flip_of_wire_ne (layout.source 0) layout.control
    (layout.control_source_ne 0).symm
  have controlAtOutput := get_flip_of_wire_ne (layout.output 0) layout.control
    (layout.control_output_ne 0).symm
  have sourceAtOutput := get_flip_of_wire_ne (layout.output 0) (layout.source 0)
    (layout.source_output_ne 0 0).symm
  cases bitValue : constant[0] <;> cases controlValue : layout.control.get state <;>
    cases sourceValue : (layout.source 0).get state <;>
      simp [topOffsetGates, lowGates, stepList, step, cnotStep, toffoliStep,
        controlAtSource, controlAtOutput, sourceAtOutput, get_flip_self,
        EncodedBit.flip_comm (layout.source 0) (layout.output 0), EncodedBit.flip_flip,
        bitValue, controlValue, sourceValue]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
