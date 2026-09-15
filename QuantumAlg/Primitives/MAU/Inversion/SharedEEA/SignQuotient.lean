/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Phase.Quotient

/-!
# Actual complete source arithmetic block 2

The baseline phase-2 swap uses the already incremented quotient length;
phase 3 swaps before decrementing [LYL+26, sec_EEA/sub_regshare.tex:281-296].
Moving both updates after the swap therefore uses old natural position
`lt + lq + (if Phase1 then 0 else 1)`, under Phase1 xor Phase2. This corrects
the missing offset in the optimized listing [ibid., sub_opt.tex:52-59;
NumberTheory.SharedEEA.SwapBoundary]. The native program executes the full
finite selector schedule followed by the actual guarded quotient update.
Its position uses an untruncated natural sum, not a caller-supplied value.

The all-label realization retains relative phases and allows arbitrary
incoming Ctrl. The source equation uses the complete algorithm's internal
Ctrl-zero invariant. Arbitrary borrowed Work2 contents are restored after
the complete selector, and arbitrary borrowed Work1 contents are restored
by the subsequent actual incrementer. No additional work bit is allocated.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SignQuotient

noncomputable section

open EncodedBit

/-- Execute the actual location selector before the actual quotient update. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  (SelectionSchedule.program width).seq (PhaseQuotient.program width)

/-- Complete frame action of the same two executable native fragments. -/
def step (width : Nat) (state : Registers width) : Registers width :=
  PhaseQuotient.step (SelectionSchedule.step width state)

/-- The source order uses the old length sum for Sign exchange and only then changes the length. -/
def sourceStep (width : Nat) (state : Registers width) : Registers width :=
  PhaseQuotient.sourceStep (SelectionSchedule.sourceStep width state)

/-- Full native realization, with no condition on the incoming quantum label. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) (step width) :=
  (SelectionSchedule.program_realizes width).seq (PhaseQuotient.program_realizes width)

private theorem indices_control (width : Nat) (indices : List (SelectionKey.Key width))
    (state : Registers width) :
    (indices.foldl (fun current selected => SelectionSwap.step width selected current)
      state).control = state.control := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ih, SelectionSwap.step_control]

/-- Both complete native fragments return the actual original Ctrl on all labels. -/
theorem step_control (width : Nat) (state : Registers width) :
    (step width state).control = state.control :=
  indices_control width (SelectionSchedule.keys width) state

private theorem source_control (width : Nat) (state : Registers width) :
    (SelectionSchedule.sourceStep width state).control = state.control := by
  by_cases within : state.coefficientLength.toNat + state.quotientLength.toNat +
      (if state.flags.first then 0 else 1) < width + 3
  · rw [SelectionSchedule.sourceStep, dif_pos within]
    by_cases selected : SelectionKey.phaseSelected state = true
    · rw [if_pos selected]
      exact SelectionSwap.exchange_control width _ state
    · rw [if_neg selected]
  · rw [SelectionSchedule.sourceStep, dif_neg within]

/-- The initialized full native block equals the actual source-selected two-operation block. -/
theorem step_eq_sourceStep (width : Nat) (state : Registers width)
    (preparedControl : state.control = false) : step width state = sourceStep width state := by
  unfold step sourceStep
  rw [SelectionSchedule.step_eq_sourceStep width state preparedControl,
    PhaseQuotient.step_eq_sourceStep _ ((source_control width state).trans preparedControl)]

/-- Exact ket execution includes the original relative phase, rather than merely the output bits. -/
theorem program_apply_prepared (width : Nat) (state : Registers width)
    (preparedControl : state.control = false) :
    (program width).applyNormalized (NormalizedVector.ket ((encoding width).encode state)) =
      NormalizedVector.ket ((encoding width).encode (sourceStep width state)) := by
  rw [(program_realizes width).apply_encoded_ket,
    step_eq_sourceStep width state preparedControl]

private theorem sign_secondWord (width : Nat) (index : Fin (width + 3)) :
    (signBit width).wire ≠ (secondWordBit width index).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [signBit_wire, secondWordBit_wire] at values
  have within := index.isLt
  omega

private theorem first_secondWord (width : Nat) (left right : Fin (width + 3)) :
    (firstWordBit width left).wire ≠ (secondWordBit width right).wire := by
  intro same
  have values := congrArg Fin.val same
  rw [firstWordBit_wire, secondWordBit_wire] at values
  have within := left.isLt
  omega

private theorem exchange_secondWord (width : Nat) (index : Fin (width + 3))
    (state : Registers width) :
    (SelectionSwap.exchange width index state).secondWord = state.secondWord := by
  apply BitVec.eq_of_getMsbD_eq
  intro bit within
  calc
    (SelectionSwap.exchange width index state).secondWord.getMsbD bit =
        (secondWordBit width ⟨bit, within⟩).get (SelectionSwap.exchange width index state) :=
      (secondWordBit_get width ⟨bit, within⟩ _).symm
    _ = (secondWordBit width ⟨bit, within⟩).get state :=
      swapStep_get_observed_of_swap_ne (signBit width) (firstWordBit width index)
        (secondWordBit width ⟨bit, within⟩) (SelectionSwap.sign_word width index)
        (sign_secondWord width ⟨bit, within⟩) (first_secondWord width index ⟨bit, within⟩) state
    _ = state.secondWord.getMsbD bit := secondWordBit_get width ⟨bit, within⟩ state

private theorem selector_secondWord (width : Nat) (selected : SelectionKey.Key width)
    (state : Registers width) :
    (SelectionSwap.step width selected state).secondWord = state.secondWord := by
  unfold SelectionSwap.step
  split
  · unfold SelectionSwap.selectedStep
    split
    · exact exchange_secondWord width _ state
    · rfl
  · rfl

private theorem indices_secondWord (width : Nat) (indices : List (SelectionKey.Key width))
    (state : Registers width) :
    (indices.foldl (fun current selected => SelectionSwap.step width selected current)
      state).secondWord = state.secondWord := by
  induction indices generalizing state with
  | nil => rfl
  | cons selected rest ih =>
      rw [List.foldl_cons, ih, selector_secondWord]

/-- Every actual borrowed Work2 bit is restored for every input, including incoming Ctrl one. -/
theorem step_secondWord (width : Nat) (state : Registers width) :
    (step width state).secondWord = state.secondWord :=
  indices_secondWord width (SelectionSchedule.keys width) state

/-- Ordered events place the complete selector, including cleanup, before the quotient fragment. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      SelectionResources.events width ++ (PhaseQuotient.program width).eventTrace := by
  rw [program, UnitaryCircuit.seq_eventTrace, SelectionResources.program_eventTrace]

/-- Literal native occurrences include the selector enumeration and the actual HRS incrementer. -/
theorem program_eventTrace_length (width : Nat) :
    (program width).eventTrace.length = SelectionResources.count width +
      (LowShiftIncrement.program width).eventTrace.length + 2 * width.size + 4 := by
  have selectorLength : (SelectionSchedule.program width).eventTrace.length =
      SelectionResources.count width := by
    rw [SelectionSchedule.program, GateSpec.programList_eventTrace, List.length_map,
      SelectionResources.gates_length]
  rw [program, UnitaryCircuit.seq_eventTrace, List.length_append, selectorLength,
    PhaseQuotient.program_eventTrace_length]
  omega

/-- The actual sequential depth preserves the dependency between the two source operations. -/
theorem program_unitDepth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = SelectionResources.count width +
      (PhaseQuotient.program width).evaluatedEventDepth (fun _ => 1) := by
  rw [program, UnitaryCircuit.evaluatedEventDepth_seq, SelectionResources.program_unitDepth]

end

end QuantumAlg.MAU.Inversion.SharedEEA.SignQuotient
