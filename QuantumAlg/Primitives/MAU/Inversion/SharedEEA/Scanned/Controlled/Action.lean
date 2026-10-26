/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Frame

/-! # Generic composition of externally selected original source actions -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSource

noncomputable section

/-- Selection changes only the full original source; all resident and external work is retained. -/
def step (width : Nat) (next : Registers width → Registers width)
    (state : ControlledFrame.Data width) : ControlledFrame.Data width :=
  ((if state.2.1 then next state.1.1 else state.1.1, state.1.2), state.2)

/-- Composition selects the ordered complete original source actions with one common control. -/
lemma step_step (width : Nat) (next first : Registers width → Registers width)
    (state : ControlledFrame.Data width) :
    step width next (step width first state) =
      step width (fun source => next (first source)) state := by
  cases selected : state.2.1 <;>
    simp only [step, selected, Bool.false_eq_true, if_false, if_true]

lemma step_disabled (width : Nat) (next : Registers width → Registers width)
    (state : ControlledFrame.Data width) (disabled : state.2.1 = false) :
    step width next state = state := by
  rw [step, disabled]
  rfl

lemma step_control (width : Nat) (next : Registers width → Registers width)
    (preserves : ∀ source, (next source).control = source.control)
    (state : ControlledFrame.Data width) :
    (step width next state).1.1.control = state.1.1.control := by
  unfold step
  split
  · exact preserves state.1.1
  · rfl

lemma step_pool (width : Nat) (next : Registers width → Registers width)
    (state : ControlledFrame.Data width) : (step width next state).1.2 = state.1.2 := rfl

lemma step_external (width : Nat) (next : Registers width → Registers width)
    (state : ControlledFrame.Data width) : (step width next state).2 = state.2 := rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSource
