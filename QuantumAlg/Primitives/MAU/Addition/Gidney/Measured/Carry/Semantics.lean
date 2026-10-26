/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Preservation
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Readout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Values

/-!
# Exact outgoing carries of the actual native dirty-output word

The induction follows the compiled recursive rows. Each dirty output retains
its original value xored with the carry computed from the original source and
quantum-control label. No carry-output initialization or separability premise
is used [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma descendingTop_control {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (state : Data) :
    layout.control.get (stepList (layout.descendingTop constant positive) state) =
      layout.control.get state :=
  descendingTop_preserves layout constant positive layout.control.get
    (get_flip_of_wire_ne (layout.output (Fin.last length)) layout.control
      (layout.control_output_ne _).symm) state

private lemma descendingTop_source {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (index : Fin (length + 1)) (state : Data) :
    (layout.source index).get (stepList (layout.descendingTop constant positive) state) =
      (layout.source index).get state :=
  descendingTop_preserves layout constant positive (layout.source index).get
    (get_flip_of_wire_ne (layout.output (Fin.last length)) (layout.source index)
      (layout.source_output_ne index _).symm) state

private lemma descendingTop_carryValues {length : Nat}
    (layout : CarryLayout encoding (length + 1)) (constant : BitVec (length + 1))
    (positive : 0 < length) (state : Data) (count : Nat) :
    layout.carryValues constant (stepList (layout.descendingTop constant positive) state) count =
      layout.carryValues constant state count :=
  carryValues_congr layout constant _ state (descendingTop_control layout constant positive state)
    (fun index => descendingTop_source layout constant positive index state) count

private lemma last_ne_castSucc {length : Nat} (index : Fin length) :
    (Fin.last length : Fin (length + 1)) ≠ index.castSucc := by
  intro equal
  have same := congrArg (fun value : Fin (length + 1) => value.val) equal
  change length = index.val at same
  have bounded := index.isLt
  omega

/-- Every actual dirty carry output is its arbitrary original bit xored with its outgoing carry. -/
lemma gates_output_get : ∀ {length : Nat} (layout : CarryLayout encoding length)
    (constant : BitVec length) (state : Data) (index : Fin length),
    (layout.output index).get (stepList (layout.gates constant) state) =
      ((layout.output index).get state ^^ layout.carryValues constant state (index.val + 1)) := by
  intro length
  induction length with
  | zero => intro _ _ _ index; exact Fin.elim0 index
  | succ length ih =>
      intro layout constant state index
      by_cases positive : 0 < length
      · let top : Fin (length + 1) := Fin.last length
        let lowerConstant := constant.setWidth length
        let before := stepList (layout.descendingTop constant positive) state
        let middle := stepList (layout.lower.gates lowerConstant) before
        let shifted := stepList (layout.topOffsetGates constant) middle
        have unroll : stepList (layout.gates constant) state =
            stepList (layout.ascendingTop constant positive) shifted := by
          rw [gates, dif_pos positive, stepList_append, stepList_append, stepList_append]
        have middleControl : layout.control.get middle = layout.control.get state := by
          exact (gates_control_get layout.lower lowerConstant before).trans
            (descendingTop_control layout constant positive state)
        have middleSource (source : Fin (length + 1)) :
            (layout.source source).get middle = (layout.source source).get state := by
          exact (gates_preserves (layout.source source).get layout.lower lowerConstant
            (fun output => get_flip_of_wire_ne (layout.output output.castSucc)
              (layout.source source) (layout.source_output_ne source output.castSucc).symm)
            before).trans (descendingTop_source layout constant positive source state)
        have shiftedControl : layout.control.get shifted = layout.control.get state := by
          exact (topOffsetGates_preserves layout constant layout.control.get
            (get_flip_of_wire_ne (layout.output top) layout.control
              (layout.control_output_ne top).symm) middle).trans middleControl
        have shiftedSource (source : Fin (length + 1)) :
            (layout.source source).get shifted = (layout.source source).get state := by
          exact (topOffsetGates_preserves layout constant (layout.source source).get
            (get_flip_of_wire_ne (layout.output top) (layout.source source)
              (layout.source_output_ne source top).symm) middle).trans (middleSource source)
        rw [unroll]
        by_cases selected : index = top
        · subst index
          let previousLow : Fin length := ⟨length - 1, by omega⟩
          let previous : Fin (length + 1) := previousLow.castSucc
          have topPrevious : top ≠ previous := last_ne_castSucc previousLow
          have beforePrevious : (layout.output previous).get before =
              (layout.output previous).get state :=
            descendingTop_preserves layout constant positive (layout.output previous).get
              (get_flip_of_wire_ne (layout.output top) (layout.output previous)
                (layout.output_ne topPrevious)) state
          have middlePrevious := ih layout.lower lowerConstant before previousLow
          change (layout.output previous).get middle =
            ((layout.output previous).get before ^^
              layout.lower.carryValues lowerConstant before (previousLow.val + 1)) at middlePrevious
          have next : previousLow.val + 1 = length := by dsimp [previousLow]; omega
          rw [next, carryValues_lower layout constant before length le_rfl,
            descendingTop_carryValues, beforePrevious] at middlePrevious
          have shiftedPrevious : (layout.output previous).get shifted =
              ((layout.output previous).get state ^^ layout.carryValues constant state length) :=
            (topOffsetGates_preserves layout constant (layout.output previous).get
              (get_flip_of_wire_ne (layout.output top) (layout.output previous)
                (layout.output_ne topPrevious)) middle).trans middlePrevious
          have middleTop : (layout.output top).get middle =
              ((layout.output top).get state ^^
                (((layout.source top).get state ^^
                  (constant.getLsbD length && layout.control.get state)) &&
                    (layout.output previous).get state)) := by
            have preserved := gates_preserves (layout.output top).get layout.lower lowerConstant
              (fun output => get_flip_of_wire_ne (layout.output output.castSucc)
                (layout.output top) (layout.output_ne (last_ne_castSucc output).symm)) before
            exact preserved.trans (descendingTop_get_output layout constant positive state)
          have shiftedTop : (layout.output top).get shifted =
              (((layout.output top).get state ^^
                (((layout.source top).get state ^^
                  (constant.getLsbD length && layout.control.get state)) &&
                    (layout.output previous).get state)) ^^
                      (constant.getLsbD length && layout.control.get state)) := by
            rw [show shifted = stepList (layout.topOffsetGates constant) middle from rfl,
              topOffsetGates_get_output, middleTop, middleControl]
          have finalCarry : layout.carryValues constant state (length + 1) =
              Bool.carry ((layout.source top).get state)
                (constant.getLsbD length && layout.control.get state)
                (layout.carryValues constant state length) := by
            rw [carryValues, dif_pos (Nat.lt_succ_self length)]
            rfl
          change (layout.output top).get
              (stepList (layout.ascendingTop constant positive) shifted) =
            ((layout.output top).get state ^^ layout.carryValues constant state (length + 1))
          rw [ascendingTop_get_output]
          change ((layout.output top).get shifted ^^
              (((layout.source top).get shifted ^^
                (constant.getLsbD length && layout.control.get shifted)) &&
                  ((layout.output previous).get shifted ^^
                    (constant.getLsbD length && layout.control.get shifted)))) = _
          rw [shiftedTop, shiftedSource, shiftedPrevious, shiftedControl, finalCarry]
          exact dirty_carry_xor ((layout.source top).get state)
            (constant.getLsbD length && layout.control.get state)
            (layout.carryValues constant state length) ((layout.output previous).get state)
            ((layout.output top).get state)
        · have inside : index.val < length := by
            have bounded := index.isLt
            have different : index.val ≠ length := fun same => selected (Fin.ext same)
            omega
          let lowerIndex : Fin length := ⟨index.val, inside⟩
          have sameIndex : lowerIndex.castSucc = index := Fin.ext rfl
          have topIndex : top ≠ index := Ne.symm selected
          calc
            _ = (layout.output index).get shifted :=
              ascendingTop_preserves layout constant positive (layout.output index).get
                (get_flip_of_wire_ne (layout.output top) (layout.output index)
                  (layout.output_ne topIndex)) shifted
            _ = (layout.output index).get middle :=
              topOffsetGates_preserves layout constant (layout.output index).get
                (get_flip_of_wire_ne (layout.output top) (layout.output index)
                  (layout.output_ne topIndex)) middle
            _ = _ := by
              have lowerRead := ih layout.lower lowerConstant before lowerIndex
              change (layout.output lowerIndex.castSucc).get middle =
                ((layout.output lowerIndex.castSucc).get before ^^
                  layout.lower.carryValues lowerConstant before (index.val + 1)) at lowerRead
              rw [sameIndex, carryValues_lower layout constant before (index.val + 1) (by omega),
                descendingTop_carryValues] at lowerRead
              have beforeIndex : (layout.output index).get before =
                  (layout.output index).get state :=
                descendingTop_preserves layout constant positive (layout.output index).get
                  (get_flip_of_wire_ne (layout.output top) (layout.output index)
                    (layout.output_ne topIndex)) state
              rw [beforeIndex] at lowerRead
              exact lowerRead
      · have zero : length = 0 := by omega
        subst length
        have selected : index = 0 := by
          apply Fin.ext
          have bounded := index.isLt
          change index.val = 0
          omega
        subst index
        rw [gates, dif_neg (by omega : ¬ 0 < 0), lowWord_get_output]
        change ((layout.output 0).get state ^^
            ((layout.source 0).get state && (constant.getLsbD 0 && layout.control.get state))) =
          ((layout.output 0).get state ^^ Bool.carry ((layout.source 0).get state)
            (constant.getLsbD 0 && layout.control.get state) false)
        cases (layout.source 0).get state <;>
          cases constant.getLsbD 0 && layout.control.get state <;> rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
