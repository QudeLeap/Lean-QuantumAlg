/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode

/-!
# Literal resources of the complete retained-clock decoder

Each actual clock-bit program repeats a real one-position inverse sweep
by that bit's fixed binary weight. All sweeps remain in the native
circuit, regardless of the input clock value. The total is exactly
`3*(n+2)*(2^(size(n)+2)-1)` elementary occurrences and strict unit depth.
Both reused high-clock positions are included
[LYL+26, sec_EEA/sub_4phase.tex:105,121-128].

These are resources of the existing adjacent-Toffoli implementation of
the repaired decoder, not the source paper's asymptotic constant. The
clock and every other non-Work2 field retain their complete values.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeResources

noncomputable section

open EncodedBit

private theorem powers_sum (count : Nat) :
    (∑ index ∈ Finset.range count, 2 ^ index) = 2 ^ count - 1 := by
  have successor : (∑ index ∈ Finset.range count, 2 ^ index) + 1 = 2 ^ count := by
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  omega

private theorem weights_sum (width : Nat) :
    ((List.finRange (width.size + 2)).map (ClockDecodeWeight.weight width)).sum =
      2 ^ (width.size + 2) - 1 := by
  rw [← Fin.sum_univ_def]
  calc
    _ = ∑ index : Fin (width.size + 2), 2 ^ index.rev.val := rfl
    _ = ∑ index : Fin (width.size + 2), 2 ^ index.val :=
      Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (width.size + 2)))
        (fun index : Fin (width.size + 2) => 2 ^ index.val)
    _ = ∑ index ∈ Finset.range (width.size + 2), 2 ^ index := by
      rw [Fin.sum_univ_eq_sum_range]
    _ = _ := powers_sum (width.size + 2)

/-- Independent closed count for every fixed bit-weighted inverse sweep in the actual decoder. -/
def count (width : Nat) : Nat := 3 * (width + 2) * (2 ^ (width.size + 2) - 1)

private theorem bit_count (width : Nat) (index : Fin (width.size + 2)) :
    (ClockDecode.bitProgram width index).eventCost.card =
      ClockDecodeWeight.weight width index * (3 * (width + 2)) := by
  rw [ClockDecode.bitProgram, UnitaryCircuit.iterate_eventCost, Multiset.card_nsmul,
    ClockDecodeBit.program, GateSpec.programList_eventCost_card, ClockDecodeBit.gates_length]

private theorem bit_depth (width : Nat) (index : Fin (width.size + 2)) :
    (ClockDecode.bitProgram width index).evaluatedEventDepth (fun _ => 1) =
      ClockDecodeWeight.weight width index * (3 * (width + 2)) := by
  rw [ClockDecode.bitProgram, UnitaryCircuit.evaluatedEventDepth_iterate,
    ClockDecodeBit.program_unitDepth]

private theorem sequence_count (width : Nat) (indices : List (Fin (width.size + 2))) :
    (ClockDecode.sequence width indices).eventCost.card =
      (indices.map (ClockDecodeWeight.weight width)).sum * (3 * (width + 2)) := by
  induction indices with
  | nil =>
    simpa only [ClockDecode.sequence, List.map_nil, List.sum_nil,
      List.length_nil, Nat.zero_mul] using
        GateSpec.programList_eventCost_card ([] : List (GateSpec (encoding width)))
  | cons index rest inductionHypothesis =>
    rw [ClockDecode.sequence, UnitaryCircuit.seq_eventCost, Multiset.card_add,
      bit_count, inductionHypothesis, List.map_cons, List.sum_cons, Nat.add_mul]

private theorem sequence_depth (width : Nat) (indices : List (Fin (width.size + 2))) :
    (ClockDecode.sequence width indices).evaluatedEventDepth (fun _ => 1) =
      (indices.map (ClockDecodeWeight.weight width)).sum * (3 * (width + 2)) := by
  induction indices with
  | nil =>
    simpa only [ClockDecode.sequence, List.map_nil, List.sum_nil,
      List.length_nil, Nat.zero_mul] using
        GateSpec.programList_evaluatedEventDepth_unit ([] : List (GateSpec (encoding width)))
  | cons index rest inductionHypothesis =>
    rw [ClockDecode.sequence, UnitaryCircuit.evaluatedEventDepth_seq, bit_depth,
      inductionHypothesis, List.map_cons, List.sum_cons, Nat.add_mul]

/-- Actual native event cardinality includes every fixed repetition for all high and low bits. -/
theorem program_event_count (width : Nat) :
    (ClockDecode.program width).eventCost.card = count width := by
  rw [ClockDecode.program, sequence_count, weights_sum, count, Nat.mul_comm]

/-- Strict unit depth counts those same serially composed native occurrences exactly. -/
theorem program_unitDepth (width : Nat) :
    (ClockDecode.program width).evaluatedEventDepth (fun _ => 1) = count width := by
  rw [ClockDecode.program, sequence_depth, weights_sum, count, Nat.mul_comm]

end

end QuantumAlg.MAU.Inversion.SharedEEA.ClockDecodeResources
