/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Preservation

/-!
# Native carry xor with one clean original low output

The descending low row has a physically clean false second control. Its
entire affine-control native word is therefore identity on the admitted
input, so the generator omits exactly that row. Every other native row
retains its original chronological order. Other carry outputs remain
arbitrary [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The original native carry rows with only the inactive clean-low descending row omitted. -/
def cleanLowGates : {length : Nat} → CarryLayout encoding length → BitVec length →
    List (GateSpec encoding)
  | 0, _, _ => []
  | length + 1, layout, constant =>
      if positive : 0 < length then
        (if 1 < length then layout.descendingTop constant positive else []) ++
          cleanLowGates layout.lower (constant.setWidth length) ++
            layout.topOffsetGates constant ++ layout.ascendingTop constant positive
      else layout.topOffsetGates constant ++ layout.lowGates constant

private lemma descending_low_identity (layout : CarryLayout encoding 2) (constant : BitVec 2)
    (state : Data) (clean : (layout.output 0).get state = false) :
    stepList (layout.descendingTop constant (by omega)) state = state := by
  rw [descendingTop_step]
  change (if ((layout.source 1).get state ^^
      (constant.getLsbD 1 && layout.control.get state)) && (layout.output 0).get state then
        (layout.output 1).flip state else state) = state
  rw [clean, Bool.and_false]
  rfl

private lemma cleanLow_two (layout : CarryLayout encoding 2) (constant : BitVec 2)
    (state : Data) (clean : (layout.output 0).get state = false) :
    stepList (layout.cleanLowGates constant) state = stepList (layout.gates constant) state := by
  rw [cleanLowGates, gates, dif_pos (by omega : 0 < 1), dif_pos (by omega : 0 < 1),
    if_neg (by omega : ¬ 1 < 1)]
  simp only [List.nil_append, stepList_append]
  rw [descending_low_identity layout constant state clean]
  rfl

/-- Omitting that one inactive native row preserves the entire original encoded-state action. -/
lemma cleanLowGates_step : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (state : Data) (positive : 0 < length),
    (layout.output ⟨0, positive⟩).get state = false →
      stepList (layout.cleanLowGates constant) state = stepList (layout.gates constant) state := by
  intro length
  induction length with
  | zero => intro layout constant state positive _; omega
  | succ length ih =>
      intro layout constant state nonempty clean
      by_cases upper : 1 < length
      · have positive : 0 < length := by omega
        let before := stepList (layout.descendingTop constant positive) state
        have topLow : (Fin.last length : Fin (length + 1)) ≠ 0 := by
          intro equal
          have values := congrArg (fun index : Fin (length + 1) => index.val) equal
          change length = 0 at values
          omega
        have retained := descendingTop_preserves layout constant positive (layout.output 0).get
          (get_flip_of_wire_ne (layout.output (Fin.last length)) (layout.output 0)
            (layout.output_ne topLow)) state
        have lowClean : (layout.lower.output ⟨0, positive⟩).get before = false := by
          change (layout.output 0).get before = false
          exact retained.trans clean
        rw [cleanLowGates, gates, dif_pos positive, dif_pos positive, if_pos upper]
        simp only [stepList_append]
        rw [ih layout.lower (constant.setWidth length) before positive lowClean]
      · have small : length = 0 ∨ length = 1 := by omega
        rcases small with zero | one
        · subst length
          rfl
        · subst length
          exact cleanLow_two layout constant state clean

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
