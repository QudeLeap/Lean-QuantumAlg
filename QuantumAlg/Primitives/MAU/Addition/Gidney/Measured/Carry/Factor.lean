/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Support
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Semantics
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Values
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Step
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Arithmetic

/-!
# Full native carry action factored into its lower word and original high carry xor

The proof follows the original descending/lower/offset/ascending source
order. The excluded high output commutes through the actual lower native
word, while its original dirty predecessor cancels between the two paid
Toffolis. No carry-output initialization is assumed
[G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private def flipWhen (target : EncodedBit encoding) (active : Bool) (state : Data) : Data :=
  if active then target.flip state else state

private lemma read_flipWhen (target observed : EncodedBit encoding)
    (different : target.wire ≠ observed.wire) (active : Bool) (state : Data) :
    observed.get (flipWhen target active state) = observed.get state := by
  cases active <;> simp [flipWhen, get_flip_of_wire_ne target observed different]

private lemma flipWhen_three (target : EncodedBit encoding) (first second third : Bool)
    (state : Data) :
    flipWhen target third (flipWhen target second (flipWhen target first state)) =
      flipWhen target ((first ^^ second) ^^ third) state := by
  cases first <;> cases second <;> cases third <;> simp [flipWhen, EncodedBit.flip_flip]

private lemma topOffset_step {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (state : Data) :
    stepList (layout.topOffsetGates constant) state =
      flipWhen (layout.output (Fin.last length))
        (constant.getLsbD length && layout.control.get state) state := by
  unfold topOffsetGates
  cases constant.getLsbD length <;> rfl

/-- The original high output is xored with its full arithmetic carry after the same lower word. -/
lemma gates_top_factor {length : Nat} (layout : CarryLayout encoding (length + 1))
    (constant : BitVec (length + 1)) (positive : 0 < length) (state : Data) :
    stepList (layout.gates constant) state =
      if layout.carryValues constant state (length + 1) then
        (layout.output (Fin.last length)).flip
          (stepList (layout.lower.gates (constant.setWidth length)) state)
      else stepList (layout.lower.gates (constant.setWidth length)) state := by
  let top := layout.output (Fin.last length)
  let previousLow : Fin length := ⟨length - 1, by omega⟩
  let previous := layout.output previousLow.castSucc
  let lower := layout.lower.gates (constant.setWidth length)
  let middle := stepList lower state
  let source := (layout.source (Fin.last length)).get state
  let offset := constant.getLsbD length && layout.control.get state
  let incoming := layout.carryValues constant state length
  let dirty := previous.get state
  let descending := (source ^^ offset) && dirty
  let ascending := (source ^^ offset) && ((dirty ^^ incoming) ^^ offset)
  have lastDifferent : (Fin.last length : Fin (length + 1)) ≠ previousLow.castSucc := by
    intro equal
    have values := congrArg (fun index : Fin (length + 1) => index.val) equal
    change length = previousLow.val at values
    have inside := previousLow.isLt
    omega
  have topControl : top.wire ≠ layout.control.wire := (layout.control_output_ne _).symm
  have topSource : top.wire ≠ (layout.source (Fin.last length)).wire :=
    (layout.source_output_ne _ _).symm
  have topPrevious : top.wire ≠ previous.wire := layout.output_ne lastDifferent
  have lowerControl : layout.control.get middle = layout.control.get state :=
    gates_control_get layout.lower (constant.setWidth length) state
  have lowerSource : (layout.source (Fin.last length)).get middle = source :=
    gates_preserves _ layout.lower (constant.setWidth length)
      (fun index => get_flip_of_wire_ne (layout.output index.castSucc)
        (layout.source (Fin.last length)) (layout.source_output_ne _ _).symm) state
  have lowerPrevious := gates_output_get layout.lower (constant.setWidth length) state previousLow
  change previous.get middle =
    (dirty ^^ layout.lower.carryValues (constant.setWidth length) state (previousLow.val + 1))
      at lowerPrevious
  have previousCount : previousLow.val + 1 = length := by dsimp [previousLow]; omega
  rw [previousCount, carryValues_lower layout constant state length le_rfl] at lowerPrevious
  have commute : stepList lower (flipWhen top descending state) =
      flipWhen top descending middle := by
    cases descending with
    | false => rfl
    | true =>
        exact gates_flip_comm layout.lower (constant.setWidth length) top
          (layout.control_output_ne _)
          (fun index => layout.source_output_ne index.castSucc _)
          (fun index => layout.output_ne (by
            intro equal
            have values := congrArg (fun value : Fin (length + 1) => value.val) equal
            change index.val = length at values
            have inside := index.isLt
            omega)) state
  have unroll : stepList (layout.gates constant) state =
      stepList (layout.ascendingTop constant positive)
        (stepList (layout.topOffsetGates constant)
          (stepList lower (flipWhen top descending state))) := by
    rw [gates, dif_pos positive, stepList_append, stepList_append, stepList_append,
      descendingTop_step]
    rfl
  have offsetEquation : stepList (layout.topOffsetGates constant)
      (flipWhen top descending middle) =
        flipWhen top offset (flipWhen top descending middle) := by
    rw [topOffset_step, read_flipWhen top layout.control topControl, lowerControl]
  have controlAfter : layout.control.get (flipWhen top offset (flipWhen top descending middle)) =
      layout.control.get state := by
    rw [read_flipWhen top layout.control topControl,
      read_flipWhen top layout.control topControl, lowerControl]
  have sourceAfter : (layout.source (Fin.last length)).get
      (flipWhen top offset (flipWhen top descending middle)) = source := by
    rw [read_flipWhen top _ topSource, read_flipWhen top _ topSource, lowerSource]
  have previousAfter : previous.get (flipWhen top offset (flipWhen top descending middle)) =
      (dirty ^^ incoming) := by
    rw [read_flipWhen top previous topPrevious, read_flipWhen top previous topPrevious,
      lowerPrevious]
  have ascendingEquation : stepList (layout.ascendingTop constant positive)
      (flipWhen top offset (flipWhen top descending middle)) =
        flipWhen top ascending (flipWhen top offset (flipWhen top descending middle)) := by
    rw [ascendingTop_step, sourceAfter, controlAfter]
    change (if (source ^^ offset) && (previous.get _ ^^ offset) then _ else _) = _
    rw [previousAfter]
    rfl
  have nextCarry : layout.carryValues constant state (length + 1) =
      Bool.carry source offset incoming := by
    rw [carryValues, dif_pos (Nat.lt_succ_self length)]
    rfl
  have combined : ((descending ^^ offset) ^^ ascending) =
      layout.carryValues constant state (length + 1) := by
    rw [nextCarry]
    have actual := dirty_carry_xor source offset incoming dirty false
    simpa only [Bool.false_xor] using actual
  rw [unroll, commute, offsetEquation, ascendingEquation, flipWhen_three, combined]
  rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.CarryLayout
