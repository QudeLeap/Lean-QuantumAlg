/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange.Source
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Exchange.Metadata
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Enable

/-! # The source exchange commutes with preparation of its separate phase enable -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange

noncomputable section

open EncodedBit

/-- The original source control is physically separate from both payload targets. -/
lemma sourceAction_control (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (sourceAction width index state).control = state.control := by
  have actual := (action_preserves width index).2 ⟨0, by omega⟩ (state, (0, (0, false)))
  change (action width index (state, (0, (0, false)))).1.control = state.control at actual
  rw [action_eq_source] at actual
  exact actual

/-- The original source exchange retains the first phase bit. -/
lemma sourceAction_phase1 (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (sourceAction width index state).flags.first = state.flags.first := by
  have actual := action_phase1 width index (state, (0, (0, false)))
  rw [action_eq_source] at actual
  exact actual

/-- The original source exchange retains the second phase bit. -/
lemma sourceAction_phase2 (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    (sourceAction width index state).flags.second = state.flags.second := by
  have actual := action_phase2 width index (state, (0, (0, false)))
  rw [action_eq_source] at actual
  exact actual

/-- The payload commutes with every XOR of its distinct original control bit. -/
lemma sourceAction_xorControl (width : Nat) (index : Fin (width + 3))
    (value : Bool) (state : Registers width) :
    sourceAction width index (NativePredicate.xorControl value state) =
      NativePredicate.xorControl value (sourceAction width index state) := by
  cases value
  · rw [NativePredicate.xorControl_false, NativePredicate.xorControl_false]
  · rw [NativePredicate.xorControl_true, NativePredicate.xorControl_true]
    apply GateSpec.stepList_flip_comm_of_bitDisjoint
    intro gate present
    simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · exact ⟨source_sign_control width, source_word_control width index⟩
    · exact ⟨source_word_control width index, source_sign_control width⟩
    · exact ⟨source_sign_control width, source_word_control width index⟩

/-- Retained phase inputs let the same paid enable computation clear after the payload. -/
lemma sourceAction_enable (width : Nat) (index : Fin (width + 3)) (state : Registers width) :
    sourceAction width index (SelectionEnable.sourceStep width state) =
      SelectionEnable.sourceStep width (sourceAction width index state) := by
  unfold SelectionEnable.sourceStep
  rw [sourceAction_phase1, sourceAction_phase2, sourceAction_xorControl]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange
