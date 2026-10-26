/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation

/-! # Complete complement preservation by actual controlled permutation words -/

namespace QuantumAlg.EncodedBit.PermutationFrame

noncomputable section

open Permutation

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {size : Nat}

/-- Every original coordinate outside the permuted word remains unchanged. -/
lemma swapAction_get_outside (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (frame.swapAction exchanges state) = observed.get state := by
  induction exchanges generalizing state with
  | nil => rfl
  | cons exchange rest ih =>
      change observed.get (frame.swapAction rest _) = _
      rw [ih, swapStep_get_observed_of_swap_ne _ _ _ (frame.targets_ne exchange)
        (outside _) (outside _)]

/-- Original outside-bit flips commute with the full unconditional permutation action. -/
lemma swapAction_flip_outside (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.bit index).wire ≠ observed.wire) (state : Data) :
    frame.swapAction exchanges (observed.flip state) =
      observed.flip (frame.swapAction exchanges state) := by
  induction exchanges generalizing state with
  | nil => rfl
  | cons exchange rest ih =>
      have one : swapStep (frame.bit exchange.first) (frame.bit exchange.second)
          (frame.targets_ne exchange) (observed.flip state) =
            observed.flip (swapStep (frame.bit exchange.first) (frame.bit exchange.second)
              (frame.targets_ne exchange) state) := by
        apply GateSpec.stepList_flip_comm_of_bitDisjoint
        intro gate present
        simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl | rfl
        · exact ⟨outside _, outside _⟩
        · exact ⟨outside _, outside _⟩
        · exact ⟨outside _, outside _⟩
      change frame.swapAction rest _ = _
      rw [one, ih]
      rfl

/-- Native control retains every complement coordinate on both control branches. -/
lemma gates_get_outside (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.bit index).wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList (frame.gates exchanges) state) = observed.get state := by
  rw [frame.gates_step]
  split
  · exact frame.swapAction_get_outside exchanges observed outside state
  · rfl

/-- The same original control survives every Fredkin in the full physical word. -/
lemma gates_get_control (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (state : Data) :
    frame.control.get (GateSpec.stepList (frame.gates exchanges) state) = frame.control.get state :=
  frame.gates_get_outside exchanges frame.control (fun index => (frame.separate index).symm) state

/-- Unused workspace and other controls remain independent of the actual controlled word. -/
lemma gates_flip_outside (frame : PermutationFrame encoding size)
    (exchanges : List (Transposition (Fin size))) (observed : EncodedBit encoding)
    (outside : ∀ index, (frame.bit index).wire ≠ observed.wire)
    (separate : observed.wire ≠ frame.control.wire) (state : Data) :
    GateSpec.stepList (frame.gates exchanges) (observed.flip state) =
      observed.flip (GateSpec.stepList (frame.gates exchanges) state) := by
  rw [frame.gates_step, frame.gates_step, get_flip_of_wire_ne observed frame.control separate]
  split
  · exact frame.swapAction_flip_outside exchanges observed outside state
  · rfl

end

end QuantumAlg.EncodedBit.PermutationFrame
