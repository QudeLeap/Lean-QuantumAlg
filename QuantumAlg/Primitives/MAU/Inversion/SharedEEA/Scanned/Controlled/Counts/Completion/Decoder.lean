/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Gates
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Bit
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Resources

/-!
# Native coordinates of the actual complete binary-weighted clock decoder

All real fixed repetitions of all original clock-bit sweeps are retained.
The numerical count follows the actual recursive concatenations, while
each sweep retains its current three-Toffoli adjacent-swap construction.
No ideal one-Toffoli replacement is substituted into the existing program.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open EncodedBit

private lemma bit_counts (width : Nat) (index : Fin (width.size + 2)) :
    ((ClockDecodeBit.gates width index).map GateSpec.toffoliMultiplicity).sum =
        3 * (width + 2) ∧
      ((ClockDecodeBit.gates width index).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((ClockDecodeBit.gates width index).map GateSpec.xMultiplicity).sum = 0 := by
  simp only [ClockDecodeBit.gates, List.map_reverse, List.sum_reverse, ClockDecodeBit.leftGates]
  refine ⟨?_, ?_, ?_⟩
  · rw [Word.controlledAdjacentShiftLeftGates_toffoliMultiplicity_sum]
    omega
  · rw [Word.controlledAdjacentShiftLeftGates_cnotMultiplicity_sum]
  · rw [Word.controlledAdjacentShiftLeftGates_xMultiplicity_sum]

private lemma repeated_weight {Gate : Type} (word : List Gate) (count : Nat)
    (weight : Gate → Nat) :
    (((List.replicate count word).flatten).map weight).sum = count * (word.map weight).sum := by
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append,
        inductionHypothesis, Nat.succ_mul]
      exact Nat.add_comm _ _

private lemma sequence_weight (width : Nat) (indices : List (Fin (width.size + 2)))
    (weight : GateSpec (SharedEEA.encoding width) → Nat) (value : Nat)
    (actual : ∀ index, ((ClockDecodeBit.gates width index).map weight).sum = value) :
    ((ClockDecode.sequenceGates width indices).map weight).sum =
      (indices.map (ClockDecodeWeight.weight width)).sum * value := by
  induction indices with
  | nil => simp [ClockDecode.sequenceGates]
  | cons index rest inductionHypothesis =>
      rw [ClockDecode.sequenceGates, List.map_append, List.sum_append, ClockDecode.bitGates,
        repeated_weight, actual, inductionHypothesis, List.map_cons, List.sum_cons, Nat.add_mul]

/-- Every actual clock-bit repetition retains its native Toffoli coordinate, with no CX or X. -/
lemma decoder_source_counts (width : Nat) :
    ((ClockDecode.gates width).map GateSpec.toffoliMultiplicity).sum =
        ClockDecodeResources.count width ∧
      ((ClockDecode.gates width).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((ClockDecode.gates width).map GateSpec.xMultiplicity).sum = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ClockDecode.gates, sequence_weight width _ _ _ (fun index => (bit_counts width index).1),
      ClockDecodeResources.weights_sum, ClockDecodeResources.count, Nat.mul_comm]
  · rw [ClockDecode.gates,
      sequence_weight width _ _ _ (fun index => (bit_counts width index).2.1), Nat.mul_zero]
  · rw [ClockDecode.gates,
      sequence_weight width _ _ _ (fun index => (bit_counts width index).2.2), Nat.mul_zero]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
