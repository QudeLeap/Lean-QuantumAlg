/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Quotient.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Control.Placement
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.LowShift.Increment

/-!
# Actual HRS increment and inverse on the retained quotient length

The optimized source increments or decrements the quotient length during
its selected Sign/word-bit exchange [LYL+26, sec_EEA/sub_opt.tex:52-59].
This owner places the existing native controlled incrementer on that
actual field. The HRS construction restores the complete arbitrary
borrowed Work1, including all of its non-target payload and padding bits
[HRS16, paper.tex:219-224]. The decrement is the literal circuit dagger.

The exact register equations hold for every finite field value and every
incoming Ctrl, including its closed branch and modular wrap. Source phase
selection and inverse cleanup are separate actual programs. No additional
cleanliness, non-overflow, or caller-domain hypothesis enters this kernel.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.QuotientIncrement

noncomputable section

private def sourceProgram (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  ControlPlacement.place width (LowShiftIncrement.program width)

/-- Reuse the actual native HRS body under the proved quotient/shift wire placement. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  QuotientPlacement.place width (sourceProgram width)

/-- The complete register action increments only the selected quotient length. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  if state.control then { state with quotientLength := state.quotientLength + 1 } else state

/-- Exact native all-label action, restoring the entire dirty Work1 and every other field. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  (QuotientPlacement.place_realizes width
    (ControlPlacement.place_realizes width (LowShiftIncrement.program_realizes width))).congrStep
    (by
      intro state
      rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
        ⟨p1, p2, sign, iter⟩, control⟩
      cases control <;> rfl)

/-- The complete inverse decrements that same finite field under the preserved control. -/
def inverseStep {width : Nat} (state : Registers width) : Registers width :=
  if state.control then { state with quotientLength := state.quotientLength - 1 } else state

private theorem step_inverseStep (width : Nat) (state : Registers width) :
    step (inverseStep state) = state := by
  rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift, flags, control⟩
  cases control <;> simp only [inverseStep, step, Bool.false_eq_true, if_false, if_true,
    BitVec.sub_add_cancel]

/-- The literal native adjoint performs finite decrement with the same fully restored work. -/
theorem inverse_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width).dagger inverseStep :=
  (program_realizes width).dagger_of_rightInverse (step_inverseStep width)

/-- Both shared words, every other retained length, and all controls are unchanged. -/
theorem step_retained {width : Nat} (state : Registers width) :
    (step state).firstWord = state.firstWord ∧
      (step state).secondWord = state.secondWord ∧
      (step state).coefficientLength = state.coefficientLength ∧
      (step state).divisorLength = state.divisorLength ∧
      (step state).shift = state.shift ∧ (step state).flags = state.flags ∧
      (step state).control = state.control := by
  cases selected : state.control <;> simp only [step, selected, Bool.false_eq_true,
    if_false, if_true, and_self]

/-- The control-zero branch retains the entire input frame exactly. -/
theorem program_apply_closed (width : Nat) (state : Registers width)
    (closed : state.control = false) :
    (program width).applyNormalized (NormalizedVector.ket ((encoding width).encode state)) =
      NormalizedVector.ket ((encoding width).encode state) := by
  rw [(program_realizes width).apply_encoded_ket]
  simp only [step, closed, Bool.false_eq_true, if_false]

/-- The quotient operation retains every actual event of the placed native HRS incrementer. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace = (LowShiftIncrement.program width).eventTrace := by
  rw [program, QuotientPlacement.place_eventTrace, sourceProgram,
    ControlPlacement.place_eventTrace]

/-- The actual decrement executes the full reversed native trace. -/
theorem inverse_eventTrace (width : Nat) :
    (program width).dagger.eventTrace = (LowShiftIncrement.program width).eventTrace.reverse := by
  rw [UnitaryCircuit.dagger_eventTrace, program_eventTrace]

private theorem source_physical_idx_subset (width : Nat) :
    (sourceProgram width).physical_idx ⊆ List.range (encoding width).width := by
  rw [sourceProgram, ControlPlacement.place_physical,
    LowShiftIncrement.program_physical]
  intro wire present
  obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp present
  have oldWithin := List.mem_range.mp oldPresent
  apply List.mem_range.mpr
  change Equiv.swap (phase2Bit width).wire.val (controlBit width).wire.val old < _
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact (controlBit width).wire.isLt
  · exact (phase2Bit width).wire.isLt
  · exact oldWithin

/-- Both target placement and all borrowed work remain inside the original complete frame. -/
theorem program_physical_idx_subset (width : Nat) :
    (program width).physical_idx ⊆ List.range (encoding width).width :=
  QuotientPlacement.place_physical_idx_subset width (sourceProgram width)
    (source_physical_idx_subset width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.QuotientIncrement
