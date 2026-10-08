/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Registers
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Literal swap on the two existing multiplication words

The swap uses the existing three-CNOT bit primitive once per word position.
Its complete two-word action is `Prod.swap`, including width zero. The
literal gate list emits exactly `3 * width` native CNOT events, with the
same unit-duration serial depth and no additional quantum systems.
-/

namespace QuantumAlg.MAU.Multiplication.Gidney

noncomputable section

open Accumulate.Gidney BinaryLabelEncoding

private def leftWord (width : Nat) : EncodedBit.Word (encoding width) width where
  bit index := prodLeftBit (finIdentity width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire index))

private def rightWord (width : Nat) : EncodedBit.Word (encoding width) width where
  bit index := prodRightBit (finIdentity width) (finIdentity width)
    (finIdentityBit width (WireAddress.littleEndianWire index))

private theorem left_get (width : Nat) (index : Fin width) (state : Registers width) :
    ((leftWord width).bit index).get state = state.1.val.testBit index.val := by
  change state.1.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem right_get (width : Nat) (index : Fin width) (state : Registers width) :
    ((rightWord width).bit index).get state = state.2.val.testBit index.val := by
  change state.2.val.testBit
    (WireAddress.bitIndex (WireAddress.littleEndianWire index)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem cross_disjoint (width : Nat) (left right : Fin width) :
    ((leftWord width).bit left).wire ≠ ((rightWord width).bit right).wire := by
  intro equality
  have values := congrArg Fin.val equality
  change width - 1 - left.val = width + (width - 1 - right.val) at values
  omega

private theorem left_disjoint (width : Nat) (left right : Fin width) (distinct : left ≠ right) :
    ((leftWord width).bit left).wire ≠ ((leftWord width).bit right).wire := by
  intro equality
  have values := congrArg Fin.val equality
  change width - 1 - left.val = width - 1 - right.val at values
  apply distinct
  apply Fin.ext
  omega

private theorem right_disjoint (width : Nat) (left right : Fin width) (distinct : left ≠ right) :
    ((rightWord width).bit left).wire ≠ ((rightWord width).bit right).wire := by
  intro equality
  have values := congrArg Fin.val equality
  change width + (width - 1 - left.val) = width + (width - 1 - right.val) at values
  apply distinct
  apply Fin.ext
  omega

/-- The actual three-CNOT swaps use only the original two words. -/
def wordSwapGates (width : Nat) : List (EncodedBit.GateSpec (encoding width)) :=
  EncodedBit.Word.swapGates (leftWord width) (rightWord width)
    (fun index => cross_disjoint width index index)

/-- The actual multiplication word swap, compiled from its literal native gate list. -/
def wordSwapProgram (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty (wordSwapGates width)

private theorem word_swap_step (width : Nat) (state : Registers width) :
    EncodedBit.Word.swapStep (leftWord width) (rightWord width)
        (fun index => cross_disjoint width index index) state = state.swap := by
  apply Prod.ext
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have readout := congrFun
      (EncodedBit.Word.swapStep_get_left_word (leftWord width) (rightWord width)
        (fun index => cross_disjoint width index index)
        (left_disjoint width) (right_disjoint width) (cross_disjoint width) state) index
    simpa only [left_get, right_get, Prod.fst_swap] using readout
  · apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have readout := congrFun
      (EncodedBit.Word.swapStep_get_right_word (leftWord width) (rightWord width)
        (fun index => cross_disjoint width index index)
        (left_disjoint width) (right_disjoint width) (cross_disjoint width) state) index
    simpa only [left_get, right_get, Prod.snd_swap] using readout

/-- The actual CNOT sequence exchanges the complete words with exact phase. -/
theorem gidneyWordSwap_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (wordSwapProgram width) Prod.swap :=
  EncodedBit.GateSpec.realizesList_congrStep _ _ _ (word_swap_step width)

/-- Exact list action of the three-CNOT swaps on all joint word labels. -/
theorem gidneyWordSwapGates_step (width : Nat) (state : Registers width) :
    EncodedBit.GateSpec.stepList (wordSwapGates width) state = state.swap :=
  word_swap_step width state

theorem gidneyWordSwap_gate_count (width : Nat) :
    (wordSwapGates width).length = 3 * width :=
  EncodedBit.Word.swapGates_length (leftWord width) (rightWord width)
    (fun index => cross_disjoint width index index)

private theorem word_swap_event (width : Nat) (gate : EncodedBit.GateSpec (encoding width))
    (present : gate ∈ wordSwapGates width) : gate.event .empty = .gate .cnot := by
  simp only [wordSwapGates, EncodedBit.Word.swapGates, List.mem_flatMap] at present
  obtain ⟨index, _, present⟩ := present
  simp only [EncodedBit.swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> rfl

/-- The full native ledger consists of exactly three CNOT occurrences per bit. -/
theorem gidneyWordSwap_eventCost (width : Nat) :
    (wordSwapProgram width).eventCost =
      ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty)
        (List.replicate (3 * width) (.gate .cnot)) := by
  rw [wordSwapProgram, EncodedBit.GateSpec.programList_eventCost]
  have events : (wordSwapGates width).map (EncodedBit.GateSpec.event .empty) =
      (wordSwapGates width).map
        (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot) := by
    apply List.map_congr_left
    exact word_swap_event width
  rw [events, List.map_const', gidneyWordSwap_gate_count]

theorem gidneyWordSwap_serial_resources (width : Nat) :
    (wordSwapProgram width).eventCost.card = 3 * width ∧
      (wordSwapProgram width).evaluatedEventDepth (fun _ => 1) = 3 * width := by
  constructor
  · exact (EncodedBit.GateSpec.programList_eventCost_card (QubitLayout.canonical _) .empty
      (wordSwapGates width)).trans
      (gidneyWordSwap_gate_count width)
  · exact (EncodedBit.GateSpec.programList_evaluatedEventDepth_unit
      (QubitLayout.canonical _) .empty (wordSwapGates width)).trans
        (gidneyWordSwap_gate_count width)

end

end QuantumAlg.MAU.Multiplication.Gidney
