/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Elementary controlled swap of the two complete supplied registers

The same control drives three literal Toffolis per pair of word positions.
The complete encoded-state equality preserves the control and swaps both words
exactly on its true branch; it imposes no initialization or separability promise.
-/

namespace QuantumAlg.EncodedRegisterSwap

noncomputable section

open EncodedBit

/-- Every swapped bit pair contributes its three actual Toffoli leaves. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.controlledSwapGates (control width) (leftWord width) (rightWord width)
    (control_left_ne width) (control_right_ne width) (fun i => left_right_ne width i i)

def program (width : Nat) : UnitaryCircuit (Qubits (1 + (width + width))) :=
  GateSpec.programList (gates width)

def step (width : Nat) : Data width → Data width := GateSpec.stepList (gates width)

/-- No temporary quantum wire appears in the elementary gate placements. -/
theorem program_physical_idx_subset (width : Nat) :
    (program width).physical_idx ⊆ List.range (1 + (width + width)) :=
  GateSpec.programList_physical_idx_subset_range _

private theorem step_control (width : Nat) (state : Data width) :
    (step width state).1 = state.1 := by
  exact Word.controlledSwapStep_get_observed_of_swap_ne
    (control width) (leftWord width) (rightWord width)
    (control_left_ne width) (control_right_ne width) (fun i => left_right_ne width i i)
    (control width) (fun i => (control_left_ne width i).symm)
    (fun i => (control_right_ne width i).symm) state

private theorem step_left_bit (width : Nat) (state : Data width) (index : Fin width) :
    (leftBit width index).get (step width state) =
      if state.1 then (rightBit width index).get state else (leftBit width index).get state :=
  Word.controlledSwapStep_get_left
    (control width) (leftWord width) (rightWord width)
    (control_left_ne width) (control_right_ne width) (fun i => left_right_ne width i i)
    index (fun _j different same => different (left_injective width same))
    (fun j => (left_right_ne width index j).symm)
    (fun j => left_right_ne width j index)
    (fun _j different same => different (right_injective width same)) state

private theorem step_right_bit (width : Nat) (state : Data width) (index : Fin width) :
    (rightBit width index).get (step width state) =
      if state.1 then (leftBit width index).get state else (rightBit width index).get state :=
  Word.controlledSwapStep_get_right
    (control width) (leftWord width) (rightWord width)
    (control_left_ne width) (control_right_ne width) (fun i => left_right_ne width i i)
    index (fun _j different same => different (left_injective width same))
    (fun j => (left_right_ne width index j).symm)
    (fun j => left_right_ne width j index)
    (fun _j different same => different (right_injective width same)) state

/-- The actual gate list has the complete controlled-swap action, including width zero. -/
theorem step_eq (width : Nat) (state : Data width) :
    step width state = (state.1, if state.1 then state.2.swap else state.2) := by
  apply Prod.ext
  · exact step_control width state
  apply Prod.ext
  · apply label_eq_of_bits
    intro index
    have actual := step_left_bit width state index
    cases branch : state.1 <;>
      simpa only [branch, Bool.false_eq_true, if_false, if_true, leftBit_get, rightBit_get,
        Prod.fst_swap, Prod.snd_swap]
        using actual
  · apply label_eq_of_bits
    intro index
    have actual := step_right_bit width state index
    cases branch : state.1 <;>
      simpa only [branch, Bool.false_eq_true, if_false, if_true, leftBit_get, rightBit_get,
        Prod.fst_swap, Prod.snd_swap]
        using actual

/-- Complete computational-basis action of the actual native program. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width)
      (fun state => (state.1, if state.1 then state.2.swap else state.2)) :=
  (GateSpec.realizesList (gates width)).congrStep (fun state => step_eq width state)

end

end QuantumAlg.EncodedRegisterSwap
