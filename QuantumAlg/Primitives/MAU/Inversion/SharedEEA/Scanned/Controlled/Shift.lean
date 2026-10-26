/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.SourceWord
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Guarded.Shift.Gates

/-!
# Actual externally fused source shifts at arbitrary original width

Both phase predicates and both literal inverse predicates receive the
real external control. The left rotation/increment and both ordered
right rotation/decrement words remain unchanged. Original internal Ctrl
starts false; no source clock range or nonzero input is assumed here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledShiftBlock

noncomputable section

open EncodedBit

/-- Only the four small predicate words are additionally controlled; every old shift executes. -/
def gates (width : Nat) (selected : Bool) : List (GateSpec (ControlledFrame.encoding width)) :=
  ControlledSourceWord.selectedGates width (PhaseGuard.firstGates width selected) ++
    ControlledSourceWord.liftedGates width (ControlledShift.leftGates width) ++
    ControlledSourceWord.selectedGates width (PhaseGuard.firstGates width selected).reverse ++
    ControlledSourceWord.selectedGates width (PhaseGuard.descendingGates width selected) ++
    ControlledSourceWord.liftedGates width (ControlledShift.rightGates width) ++
    ControlledSourceWord.liftedGates width (ControlledShift.rightGates width) ++
    ControlledSourceWord.selectedGates width (PhaseGuard.descendingGates width selected).reverse

def step (width : Nat) (selected : Bool) (state : ControlledFrame.Data width) :
    ControlledFrame.Data width :=
  ((if state.2.1 then GuardedShift.step selected state.1.1 else state.1.1, state.1.2), state.2)

private lemma gates_step (width : Nat) (selected : Bool) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) :
    GateSpec.stepList (gates width selected) state = step width selected state := by
  simp only [gates, GateSpec.stepList_append, ControlledSourceWord.selectedGates_step,
    ControlledSourceWord.liftedGates_step, PhaseGuard.first_step, PhaseGuard.first_reverse_step,
    PhaseGuard.descending_step, PhaseGuard.descending_reverse_step,
    ControlledShift.controlledShift_leftGates_step,
    ControlledShift.controlledShift_rightGates_step]
  rcases state with ⟨⟨⟨word1, word2, lengthT, lengthQ, lengthR, shift,
    ⟨p1, p2, sign, iteration⟩, internal⟩, pool⟩, ⟨external, work⟩⟩
  change internal = false at control
  subst internal
  cases external <;> cases selected <;> cases p1 <;> cases p2 <;> rfl

def program (width : Nat) (selected : Bool) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (ControlledFrame.encoding width).width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates width selected)

/-- The real full native shift restores every original pool and arbitrary external work state. -/
lemma program_apply_encoded_ket (width : Nat) (selected : Bool)
    (environment : OracleModel.empty.Interpretation) (state : ControlledFrame.Data width)
    (control : state.1.1.control = false) :
    (program width selected).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((ControlledFrame.encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((ControlledFrame.encoding width).encode (step width selected state))) := by
  have actual := (GateSpec.realizesList (QubitLayout.canonical _) .empty
    (gates width selected) environment).apply_encoded_ket state
  rw [gates_step width selected state control] at actual
  exact actual

lemma step_disabled (width : Nat) (selected : Bool) (state : ControlledFrame.Data width)
    (disabled : state.2.1 = false) : step width selected state = state := by
  rw [step, disabled]
  rfl

lemma step_pool (width : Nat) (selected : Bool) (state : ControlledFrame.Data width) :
    (step width selected state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (selected : Bool) (state : ControlledFrame.Data width) :
    (step width selected state).2 = state.2 := rfl

lemma step_control (width : Nat) (selected : Bool) (state : ControlledFrame.Data width) :
    (step width selected state).1.1.control = state.1.1.control := by
  unfold step
  split
  · exact GuardedShift.step_control width selected state.1.1
  · rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledShiftBlock
