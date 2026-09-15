/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Program
import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Swap
import all QuantumAlg.Components.Encoded.BitGates.Swap
import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Exact native occurrences in the controlled register swap

The ledger counts the actual Toffoli list, with three gates per bit pair and
no preparation, measurement, classical instruction or extra quantum system.
-/

namespace QuantumAlg.EncodedRegisterSwap

noncomputable section

open EncodedBit

private theorem indices_trace (width : Nat) (indices : List (Fin width)) :
    (indices.flatMap fun i => EncodedBit.controlledSwapGates
      (control width) (leftBit width i) (rightBit width i)
      (control_left_ne width i) (control_right_ne width i) (left_right_ne width i i)).map
        GateSpec.event = List.replicate (3 * indices.length) (.gate (.builtin "toffoli")) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [List.flatMap_cons, List.map_append, ih]
    simp only [EncodedBit.controlledSwapGates, List.map_cons, List.map_nil,
      GateSpec.event, List.length_cons]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm, List.replicate_add]
    rfl

/-- Exactly three elementary Toffoli occurrences per original word position. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      List.replicate (3 * width) (.gate (.builtin "toffoli")) := by
  calc
    _ = (gates width).map GateSpec.event := GateSpec.programList_eventTrace _
    _ = _ := by
      change ((List.ofFn fun i : Fin width => i).flatMap fun i =>
        EncodedBit.controlledSwapGates (control width) (leftBit width i) (rightBit width i)
          (control_left_ne width i) (control_right_ne width i)
          (left_right_ne width i i)).map GateSpec.event = _
      rw [indices_trace, List.length_ofFn]

theorem program_eventTrace_length (width : Nat) :
    (program width).eventTrace.length = 3 * width := by
  rw [program_eventTrace, List.length_replicate]

end

end QuantumAlg.EncodedRegisterSwap
