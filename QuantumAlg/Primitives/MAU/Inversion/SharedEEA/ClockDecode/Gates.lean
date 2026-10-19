/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Resources

/-!
# Literal instructions of the complete retained-clock decoder

The existing decoder repeats its three-Toffoli adjacent swaps by fixed
binary weights. This list exposes precisely those repetitions in execution
order. Its action preserves the complete original clock and history, and its
native trace and resource count equal the existing decoder's exact quantities.
The exposed instructions can subsequently receive physical gate-local control.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ClockDecode

noncomputable section

open NumberTheory.SharedEEA EncodedBit GateSpec PredicateLayout

private lemma repeated_step {Data : Type} {source : BinaryLabelEncoding Data}
    (instructions : List (GateSpec source)) (count : Nat) (state : Data) :
    stepList (List.replicate count instructions).flatten state =
      (stepList instructions)^[count] state := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatten_cons, stepList_append, ih,
        Function.iterate_succ_apply]

/-- Fixed binary repetitions of the actual one-clock-bit adjacent-swap instructions. -/
def bitGates (width : Nat) (index : Fin (width.size + 2)) :
    List (GateSpec (encoding width)) :=
  (List.replicate (ClockDecodeWeight.weight width index)
    (ClockDecodeBit.gates width index)).flatten

private lemma bitGates_step (width : Nat) (index : Fin (width.size + 2))
    (state : Registers width) :
    stepList (bitGates width index) state = rotateFrame state
      (((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index) := by
  have same : stepList (ClockDecodeBit.gates width index) = bitStep width index :=
    funext (ClockDecodeBit.gates_step width index)
  rw [bitGates, repeated_step, same, bit_iterate]

private lemma bitGates_trace (width : Nat) (index : Fin (width.size + 2)) :
    (bitGates width index).map (event .empty) = (bitProgram width index).eventTrace := by
  rw [bitProgram, UnitaryCircuit.iterate_eventTrace, ClockDecodeBit.program_eventTrace]
  simp only [bitGates, List.map_flatten, List.map_replicate]

private def sequenceGates (width : Nat) :
    List (Fin (width.size + 2)) → List (GateSpec (encoding width))
  | [] => []
  | index :: rest => bitGates width index ++ sequenceGates width rest

private lemma sequenceGates_step (width : Nat) (indices : List (Fin (width.size + 2)))
    (state : Registers width) :
    stepList (sequenceGates width indices) state = rotateFrame state
      ((indices.map fun index =>
        ((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index).sum) := by
  induction indices generalizing state with
  | nil => exact (rotateFrame_zero state).symm
  | cons index rest ih =>
      rw [sequenceGates, stepList_append, bitGates_step, ih]
      let count := ((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index
      have retained : (rest.map fun position =>
          ((clockBit width position).get (rotateFrame state count)).toNat *
            ClockDecodeWeight.weight width position) =
          rest.map (fun position => ((clockBit width position).get state).toNat *
            ClockDecodeWeight.weight width position) := by
        apply List.map_congr_left
        intro position _
        rw [control_rotateFrame]
      change rotateFrame (rotateFrame state count) _ = _
      rw [retained, rotateFrame_comp]
      rfl

private lemma sequenceGates_trace (width : Nat) (indices : List (Fin (width.size + 2))) :
    (sequenceGates width indices).map (event .empty) = (sequence width indices).eventTrace := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      rw [sequenceGates, List.map_append, bitGates_trace, ih, sequence,
        UnitaryCircuit.seq_eventTrace]

/-- Every actual instruction of the complete weighted decoder, with all original repetitions. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  sequenceGates width (List.finRange (width.size + 2))

/-- The literal list rotates exactly by the retained complete clock and keeps every other field. -/
lemma clockDecode_gates_step (width : Nat) (state : Registers width) :
    stepList (gates width) state =
      { state with secondWord :=
          state.secondWord.rotateRight (ExtendedClockRegisters.clock state).toNat } := by
  rw [gates, sequenceGates_step]
  have total : ((List.finRange (width.size + 2)).map fun index =>
      ((clockBit width index).get state).toNat * ClockDecodeWeight.weight width index).sum =
        (ExtendedClockRegisters.clock state).toNat := by
    rw [← Fin.sum_univ_def]
    exact ClockDecodeWeight.selected_sum width state
  exact congrArg (rotateFrame state) total

/-- Flattening retains the exact execution order, including every fixed repeated native gate. -/
lemma clockDecode_gates_trace (width : Nat) :
    (gates width).map (event .empty) = (program width).eventTrace :=
  sequenceGates_trace width (List.finRange (width.size + 2))

/-- Every resource coordinate agrees with the original symbolic decoder. -/
lemma clockDecode_gates_eventCost (width : Nat) :
    ResourcePool.ofList ((gates width).map (event .empty)) = (program width).eventCost := by
  rw [clockDecode_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The actual list has the same exact weighted count, with no new gate or ancillary wire. -/
lemma clockDecode_gates_length (width : Nat) :
    (gates width).length = ClockDecodeResources.count width := by
  have count := congrArg Multiset.card (clockDecode_gates_eventCost width)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at count
  exact count.trans (ClockDecodeResources.program_event_count width)

end

end QuantumAlg.MAU.Inversion.SharedEEA.ClockDecode
