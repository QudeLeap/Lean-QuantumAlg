/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.ManyDirty.Test
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy.Resources
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Resources

/-!
# Exact charged native trace with an existing arbitrary borrowed bank

Small cases retain their literal CNOT or Toffoli. Every larger complete
test retains its actual paired dirty conjunction sandwiches and both
source masks. The complete existing bank returns on every input.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent exact complete test trace, including every negative-control mask. -/
def manyDirtyTrace (count : Nat) : List (Resource.Event (.quantum AlgorithmGate.model .empty)) :=
  List.replicate count (.gate .singleQubit) ++
    (if count = 0 then [.gate .cnot] else
      List.replicate (if count = 1 then 1 else 4 * (count - 1)) (.gate .toffoli)) ++
    List.replicate count (.gate .singleQubit)

private lemma borrowedAnd_events {Data : Type} {encoding : BinaryLabelEncoding Data}
    {tail : Nat} (layout : Word.ZeroTestLayout (encoding := encoding) tail) :
    layout.borrowedAndGates.map (GateSpec.event .empty) =
      List.replicate (if tail = 0 then 1 else 4 * tail) (.gate .toffoli) := by
  apply List.eq_replicate_iff.mpr
  constructor
  · rw [List.length_map]
    by_cases empty : tail = 0
    · rw [Word.ZeroTestLayout.borrowedAndGates, if_pos empty, if_pos empty]
      rfl
    · rw [Word.ZeroTestLayout.borrowedAndGates, if_neg empty, if_neg empty]
      exact Word.ZeroTestLayout.dirtyConjunctionGates_length layout (Nat.pos_of_ne_zero empty)
  · intro event member
    obtain ⟨gate, present, rfl⟩ := List.mem_map.mp member
    exact Word.ZeroTestLayout.borrowedAndGates_event .empty layout gate present

namespace Frame.BorrowedBank

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {count outputWidth depth bankWidth : Nat} {frame : Frame encoding count outputWidth depth}
  (bank : frame.BorrowedBank bankWidth)

/-- The same actual complete native test word has the exact independent original-subword trace. -/
lemma manyDirtyTest_events (labels : List (Fin count)) (unique : labels.Nodup)
    (level : Nat) (present : level < depth) :
    (bank.testGates labels unique level present).map (GateSpec.event .empty) =
      manyDirtyTrace labels.length := by
  cases labels with
  | nil => rfl
  | cons head rest =>
      let original := frame.testLayout (head :: rest) unique level present
      have maskEvents : (original.patternMaskGates (fun _ => false)).map (GateSpec.event .empty) =
          List.replicate (head :: rest).length (.gate .singleQubit) := by
        rw [Word.OneDirtyLayout.patternMaskGates]
        simp only [List.map_map]
        change (Word.OneDirtyLayout.patternMaskIndices
          (fun _ : Fin (head :: rest).length => false)).map
          (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty)
            .singleQubit) = _
        rw [List.map_const']
        simp only [Word.OneDirtyLayout.patternMaskIndices, Bool.not_false, List.filter_true,
          List.length_ofFn]
      rw [testGates, List.map_append, List.map_append, List.map_reverse, maskEvents,
        borrowedAnd_events, List.reverse_replicate]
      by_cases empty : rest.length = 0
      · simp only [manyDirtyTrace, List.length_cons, empty, Nat.zero_add, Nat.one_ne_zero,
          if_false, if_true]
      · have nonzero : rest.length + 1 ≠ 0 := by omega
        have notOne : rest.length + 1 ≠ 1 := by omega
        simp only [manyDirtyTrace, List.length_cons, if_neg nonzero, if_neg notOne,
          if_neg empty, Nat.add_sub_cancel]

/-- All exact native coordinates come from the same full actual bank-restoring encoder. -/
lemma manyDirtyEncoder_eventCost (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (bank.policy.encoderProgram height capacity fits).eventCost =
      ResourcePool.ofList (policyEncoderTrace manyDirtyTrace count outputWidth height) :=
  bank.policy.policyEncoderProgram_eventCost manyDirtyTrace bank.manyDirtyTest_events
    height capacity fits

/-- The actual entire native quantum duration is its complete paid policy trace length. -/
lemma manyDirtyEncoder_quantumDuration (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (bank.policy.encoderProgram height capacity fits).evaluatedEventDepth
        Resource.Event.quantumDuration =
      (policyEncoderTrace manyDirtyTrace count outputWidth height).length :=
  bank.policy.policyEncoderProgram_quantumDuration manyDirtyTrace bank.manyDirtyTest_events
    height capacity fits

end Frame.BorrowedBank

end

end QuantumAlg.EncodedBit.FirstOne
