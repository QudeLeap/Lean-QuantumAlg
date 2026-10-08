/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Key
import all QuantumAlg.Components.Encoded.BitGates.Controlled.SwapLaws

/-!
# One actual finite Sign/Work1 selector with complete inverse cleanup

Each fixed key compares the complete original lengths and both phases,
then executes three actual Toffolis exchanging Sign with the indicated
Work1 bit. The predicate is then reversed. The physical position uses the
untruncated natural sum of the key's two length values plus one in phase 2.
An out-of-range index emits an empty list. The extra phase-2 position
retains the baseline's increment-before-swap boundary
[LYL+26, sec_EEA/sub_regshare.tex:281-296], correcting the missing offset
after the optimized listing moves that increment past the swap
[ibid., sub_opt.tex:52-59; NumberTheory.SharedEEA.SwapBoundary].

The native all-label law allows arbitrary Ctrl. On the internally prepared
Ctrl-zero subspace only the matching key acts. Both predicate passes restore
arbitrary Work2 contents, and the selected swap is disjoint from every
length/phase source coordinate. No caller promise supplies a clean work
word, a classical copy of a quantum length, or a non-overflow certificate.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionSwap

noncomputable section

open EncodedBit NativePredicate SelectionLayout SelectionKey

private theorem control_sign (width : Nat) :
    (controlBit width).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, signBit_wire] at values
  omega

private theorem control_word (width : Nat) (index : Fin (width + 3)) :
    (controlBit width).wire ≠ (firstWordBit width index).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [controlBit_wire, firstWordBit_wire] at values
  have within := index.isLt
  omega

private theorem sign_word (width : Nat) (index : Fin (width + 3)) :
    (signBit width).wire ≠ (firstWordBit width index).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [signBit_wire, firstWordBit_wire] at values
  have within := index.isLt
  omega

private theorem source_sign (width : Nat) (index : Fin (2 * width.size + 2)) :
    ((layout width).source.bit index).wire ≠ (signBit width).wire := by
  intro same
  have values := congrArg Fin.val same
  change (sourceBit width index).wire.val = (signBit width).wire.val at values
  rw [sourceBit_wire, signBit_wire] at values
  have within := index.isLt
  unfold physicalIndex at values
  split_ifs at values <;> omega

private theorem word_source (width : Nat) (wordIndex : Fin (width + 3))
    (sourceIndex : Fin (2 * width.size + 2)) :
    (firstWordBit width wordIndex).wire ≠ ((layout width).source.bit sourceIndex).wire := by
  intro same
  have values := congrArg Fin.val same
  change (firstWordBit width wordIndex).wire.val = (sourceBit width sourceIndex).wire.val at values
  rw [firstWordBit_wire, sourceBit_wire] at values
  have within := wordIndex.isLt
  unfold physicalIndex at values
  split_ifs at values <;> omega

/-- The canonical exact exchange of Sign and one original Work1 coordinate. -/
def exchange (width : Nat) (index : Fin (width + 3)) (state : Registers width) : Registers width :=
  swapStep (signBit width) (firstWordBit width index) (sign_word width index) state

/-- The entire original control is outside both exchanged targets. -/
theorem exchange_control (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (exchange width index state).control = state.control :=
  swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width index) (controlBit width)
    (sign_word width index) (control_sign width).symm (control_word width index).symm state

/-- Every bit used to select a key is restored by the canonical target exchange. -/
theorem exchange_source_get (width : Nat) (index : Fin (width + 3))
    (sourceIndex : Fin (2 * width.size + 2)) (state : Registers width) :
    ((layout width).source.bit sourceIndex).get (exchange width index state) =
      ((layout width).source.bit sourceIndex).get state :=
  swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width index)
    ((layout width).source.bit sourceIndex) (sign_word width index)
    (source_sign width sourceIndex).symm (word_source width index sourceIndex) state

/-- The actual selected Work1 bit becomes Sign. -/
theorem exchange_sign (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (exchange width index state).flags.sign = state.firstWord.getMsbD index.val :=
  (swapStep_get_left (signBit width) (firstWordBit width index) (sign_word width index) state).trans
    (firstWordBit_get width index state)

/-- The original Sign becomes the actual selected Work1 bit. -/
theorem exchange_wordBit (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (exchange width index state).firstWord.getMsbD index.val = state.flags.sign :=
  (firstWordBit_get width index (exchange width index state)).symm.trans
    (swapStep_get_right (signBit width) (firstWordBit width index) (sign_word width index) state)

/-- Every source equality predicate is unchanged by the selected target exchange. -/
theorem exchange_condition (width : Nat) (index : Fin (width + 3))
    (expected : SelectionPredicate.Pattern width) (state : Registers width) :
    SelectionPredicate.condition expected (exchange width index state) =
      SelectionPredicate.condition expected state := by
  simp only [SelectionPredicate.condition, SelectionPredicate.Matches, exchange_source_get]

private theorem exchange_xorControl (width : Nat) (index : Fin (width + 3))
    (value : Bool) (state : Registers width) :
    exchange width index (xorControl value state) =
      xorControl value (exchange width index state) := by
  cases value
  · rw [NativePredicate.xorControl_false, NativePredicate.xorControl_false]
  · rw [NativePredicate.xorControl_true, NativePredicate.xorControl_true]
    apply GateSpec.stepList_flip_comm_of_bitDisjoint
    intro gate present
    simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact ⟨(control_sign width).symm, (control_word width index).symm⟩
    · exact ⟨(control_word width index).symm, (control_sign width).symm⟩
    · exact ⟨(control_sign width).symm, (control_word width index).symm⟩

private def targetGates (width : Nat) (index : Fin (width + 3)) :
    List (GateSpec (encoding width)) :=
  EncodedBit.controlledSwapGates (controlBit width) (signBit width) (firstWordBit width index)
    (control_sign width) (control_word width index) (sign_word width index)

private theorem targetGates_step (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    GateSpec.stepList (targetGates width index) state =
      if state.control then exchange width index state else state :=
  EncodedBit.controlledSwapStep_eq_if (controlBit width) (signBit width) (firstWordBit width index)
    (control_sign width) (control_word width index) (sign_word width index) state

private def selectedStep (width : Nat) (selected : Key width) (index : Fin (width + 3))
    (state : Registers width) : Registers width :=
  if state.control ^^ SelectionPredicate.condition (pattern selected) state
  then exchange width index state else state

private theorem selectedStep_condition (width : Nat) (selected : Key width)
    (index : Fin (width + 3)) (expected : SelectionPredicate.Pattern width)
    (state : Registers width) :
    SelectionPredicate.condition expected (selectedStep width selected index state) =
      SelectionPredicate.condition expected state := by
  unfold selectedStep
  split
  · exact exchange_condition width index expected state
  · rfl

private theorem target_computed (width : Nat) (selected : Key width) (index : Fin (width + 3))
    (state : Registers width) :
    GateSpec.stepList (targetGates width index)
        (xorControl (SelectionPredicate.condition (pattern selected) state) state) =
      xorControl (SelectionPredicate.condition (pattern selected) state)
        (selectedStep width selected index state) := by
  rw [targetGates_step]
  change (if state.control ^^ SelectionPredicate.condition (pattern selected) state then
    exchange width index (xorControl (SelectionPredicate.condition (pattern selected) state) state)
    else xorControl (SelectionPredicate.condition (pattern selected) state) state) = _
  unfold selectedStep
  split
  · exact exchange_xorControl width index _ state
  · rfl

private def selectedGates (width : Nat) (selected : Key width) (index : Fin (width + 3)) :
    List (GateSpec (encoding width)) :=
  SelectionPredicate.gates width (pattern selected) ++ targetGates width index ++
    (SelectionPredicate.gates width (pattern selected)).reverse

private theorem selectedGates_step (width : Nat) (selected : Key width)
    (index : Fin (width + 3)) (state : Registers width) :
    GateSpec.stepList (selectedGates width selected index) state =
      selectedStep width selected index state := by
  rw [selectedGates, GateSpec.stepList_append, GateSpec.stepList_append,
    SelectionPredicate.gates_step, target_computed, SelectionPredicate.reverse_step,
    SelectionPredicate.condition_xorControl, selectedStep_condition, xorControl_twice]

/-- Out-of-range natural positions emit no native operation; valid positions use actual gates. -/
def gates (width : Nat) (selected : Key width) : List (GateSpec (encoding width)) :=
  if within : position selected < width + 3 then
    selectedGates width selected ⟨position selected, within⟩ else []

/-- Full actual selector action, including out-of-range and arbitrary incoming Ctrl branches. -/
def step (width : Nat) (selected : Key width) (state : Registers width) : Registers width :=
  if within : position selected < width + 3 then
    selectedStep width selected ⟨position selected, within⟩ state else state

theorem gates_step (width : Nat) (selected : Key width) (state : Registers width) :
    GateSpec.stepList (gates width selected) state = step width selected state := by
  unfold gates step
  split
  · exact selectedGates_step width selected _ state
  · rfl

/-- The entire original Ctrl survives each complete selector, not just the successful one. -/
theorem step_control (width : Nat) (selected : Key width) (state : Registers width) :
    (step width selected state).control = state.control := by
  unfold step
  split
  · unfold selectedStep
    split
    · exact exchange_control width _ state
    · rfl
  · rfl

/-- Every other key's equality value is also retained after this complete selector. -/
theorem step_condition (width : Nat) (selected : Key width)
    (expected : SelectionPredicate.Pattern width) (state : Registers width) :
    SelectionPredicate.condition expected (step width selected state) =
      SelectionPredicate.condition expected state := by
  unfold step
  split
  · exact selectedStep_condition width selected _ expected state
  · rfl

/-- The complete actual predicate/swap/inverse-predicate native program for one finite key. -/
def program (width : Nat) (selected : Key width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width selected)

/-- Exact all-label realization of that same complete native list. -/
theorem program_realizes (width : Nat) (selected : Key width) :
    UnitaryCircuit.Realizes (encoding width) (program width selected) (step width selected) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
    (gates width selected) (gates_step width selected)

/-- Literal count of both full predicate passes and the three actual swap Toffolis. -/
theorem gates_length (width : Nat) (selected : Key width) :
    (gates width selected).length =
      if position selected < width + 3 then
        2 * (SelectionPredicate.gates width (pattern selected)).length + 3 else 0 := by
  unfold gates
  split
  · simp only [selectedGates, List.length_append, List.length_reverse,
      targetGates, EncodedBit.controlledSwapGates, List.length_cons, List.length_nil]
    omega
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionSwap
