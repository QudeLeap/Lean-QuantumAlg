/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Parallel.Frame

/-!
# Reordering separate permutation payloads with retained controls

The controls may coincide. These are exact full-state reordering laws,
not a license to put gates with a shared control in one native layer.
-/

namespace QuantumAlg.EncodedBit.PermutationFrame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {leftSize rightSize : Nat}

private lemma gates_cnot_comm (left : PermutationFrame encoding leftSize)
    (exchanges : List (Permutation.Transposition (Fin leftSize)))
    (source target : EncodedBit encoding)
    (sourceOutside : ∀ index, (left.bit index).wire ≠ source.wire)
    (targetOutside : ∀ index, (left.bit index).wire ≠ target.wire)
    (targetControl : target.wire ≠ left.control.wire) (state : Data) :
    GateSpec.stepList (left.gates exchanges) (cnotStep source target state) =
      cnotStep source target (GateSpec.stepList (left.gates exchanges) state) := by
  unfold cnotStep
  rw [left.gates_get_outside exchanges source sourceOutside state]
  split
  · exact left.gates_flip_outside exchanges target targetOutside targetControl state
  · rfl

private lemma gates_swap_comm (left : PermutationFrame encoding leftSize)
    (exchanges : List (Permutation.Transposition (Fin leftSize)))
    (first second : EncodedBit encoding) (different : first.wire ≠ second.wire)
    (firstOutside : ∀ index, (left.bit index).wire ≠ first.wire)
    (secondOutside : ∀ index, (left.bit index).wire ≠ second.wire)
    (firstControl : first.wire ≠ left.control.wire)
    (secondControl : second.wire ≠ left.control.wire) (state : Data) :
    GateSpec.stepList (left.gates exchanges) (swapStep first second different state) =
      swapStep first second different (GateSpec.stepList (left.gates exchanges) state) := by
  change GateSpec.stepList (left.gates exchanges)
    (cnotStep first second (cnotStep second first (cnotStep first second state))) =
    cnotStep first second (cnotStep second first
      (cnotStep first second (GateSpec.stepList (left.gates exchanges) state)))
  rw [gates_cnot_comm left exchanges first second firstOutside secondOutside secondControl,
    gates_cnot_comm left exchanges second first secondOutside firstOutside firstControl,
    gates_cnot_comm left exchanges first second firstOutside secondOutside secondControl]

private lemma gates_swapAction_comm (left : PermutationFrame encoding leftSize)
    (right : PermutationFrame encoding rightSize)
    (first : List (Permutation.Transposition (Fin leftSize)))
    (second : List (Permutation.Transposition (Fin rightSize)))
    (cross : ∀ i j, (left.bit i).wire ≠ (right.bit j).wire)
    (controlOutside : ∀ j, left.control.wire ≠ (right.bit j).wire) (state : Data) :
    GateSpec.stepList (left.gates first) (right.swapAction second state) =
      right.swapAction second (GateSpec.stepList (left.gates first) state) := by
  induction second generalizing state with
  | nil => rfl
  | cons exchange rest ih =>
      change GateSpec.stepList (left.gates first) (right.swapAction rest
        (swapStep (right.bit exchange.first) (right.bit exchange.second) _ state)) = _
      rw [ih, gates_swap_comm left first _ _ _
        (fun index => cross index exchange.first) (fun index => cross index exchange.second)
        (controlOutside exchange.first).symm (controlOutside exchange.second).symm]
      rfl

/-- Complete native words commute when their targets are separate from the other full word
and its retained control; the controls themselves may be the same physical system. -/
lemma gates_comm (left : PermutationFrame encoding leftSize)
    (right : PermutationFrame encoding rightSize)
    (first : List (Permutation.Transposition (Fin leftSize)))
    (second : List (Permutation.Transposition (Fin rightSize)))
    (cross : ∀ i j, (left.bit i).wire ≠ (right.bit j).wire)
    (leftControl : ∀ j, left.control.wire ≠ (right.bit j).wire)
    (rightControl : ∀ i, right.control.wire ≠ (left.bit i).wire) (state : Data) :
    GateSpec.stepList (left.gates first) (GateSpec.stepList (right.gates second) state) =
      GateSpec.stepList (right.gates second) (GateSpec.stepList (left.gates first) state) := by
  rw [right.gates_step, right.gates_step,
    left.gates_get_outside first right.control (fun index => (rightControl index).symm) state]
  split
  · exact gates_swapAction_comm left right first second cross leftControl state
  · rfl

end

end QuantumAlg.EncodedBit.PermutationFrame
