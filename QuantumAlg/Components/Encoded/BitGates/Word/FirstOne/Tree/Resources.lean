/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Zero.Resources
import all QuantumAlg.Util.List.PriorityTree.Work

/-!
# Actual recursive native first-one trace and complete work bound

Both child programs, both complete controlled subword tests and both
prefix CNOTs appear in their real execution order. The bound charges
all mask gates, the arbitrary-work conjunction and every output leaf.
-/

namespace QuantumAlg.EncodedBit.FirstOne

noncomputable section

/-- Independent exact native trace of the recursive emitter on the original static priority tree. -/
def emitterTrace {count : Nat} (outputWidth : Nat) : ListPriority.Tree (Fin count) →
    List (Resource.Event (.quantum AlgorithmGate.model .empty))
  | .empty => []
  | .leaf label => List.replicate
      (Word.constantOneIndices (Frame.leafMask (outputWidth := outputWidth) label)).length
      (.gate .toffoli)
  | .fork higher lower => zeroTrace higher.leaves.length ++
      (emitterTrace outputWidth lower ++ (.gate .cnot ::
        (emitterTrace outputWidth higher ++ (zeroTrace higher.leaves.length ++ [.gate .cnot]))))

namespace Frame

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Every complete actual subword test has its declared exact native ordered trace. -/
lemma testGates_events (labels : List (Fin count)) (distinct : labels.Nodup)
    (level : Nat) (present : level < depth) :
    (frame.testGates labels distinct level present).map (GateSpec.event .empty) =
      zeroTrace labels.length :=
  zeroGates_events _ _ _ _ _

/-- The complete recursive literal word has exactly the independent original-tree trace. -/
lemma gatesAt_events (tree : ListPriority.Tree (Fin count)) (distinct : tree.leaves.Nodup)
    (level : Nat) (fits : level + tree.height ≤ depth) :
    (frame.gatesAt tree distinct level fits).map (GateSpec.event .empty) =
      emitterTrace outputWidth tree := by
  induction tree generalizing level with
  | empty => rfl
  | leaf label =>
      simp only [gatesAt, Word.doubleControlledXorConstantGates, List.map_map, emitterTrace]
      change (Word.constantOneIndices (leafMask (outputWidth := outputWidth) label)).map
        (fun _ => Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .toffoli) = _
      simp
  | fork higher lower higherTrace lowerTrace =>
      dsimp only [gatesAt, emitterTrace]
      simp only [List.map_append, List.map_cons, List.map_nil, frame.testGates_events,
        lowerTrace, higherTrace]
      rfl

/-- The literal recursive word is bounded by all tested source occurrences and actual forks. -/
lemma gatesAt_length_le (tree : ListPriority.Tree (Fin count)) (distinct : tree.leaves.Nodup)
    (level : Nat) (fits : level + tree.height ≤ depth) :
    (frame.gatesAt tree distinct level fits).length ≤
      outputWidth * tree.leaves.length + 20 * tree.testVolume + 24 * tree.forks := by
  induction tree generalizing level with
  | empty => exact Nat.le_refl _
  | leaf label =>
      simpa only [gatesAt, Word.doubleControlledXorConstantGates, List.length_map,
        ListPriority.Tree.leaves, List.length_singleton, ListPriority.Tree.testVolume,
        ListPriority.Tree.forks, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using
          Word.constantOneIndices_length_le (leafMask (outputWidth := outputWidth) label)
  | fork higher lower higherBound lowerBound =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      have higherDistinct := (List.nodup_append.mp distinct).1
      have lowerDistinct := (List.nodup_append.mp distinct).2.1
      have higherFits : level + 1 + higher.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).1
        omega
      have lowerFits : level + 1 + lower.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).2
        omega
      have higherLength := higherBound higherDistinct (level + 1) higherFits
      have lowerLength := lowerBound lowerDistinct (level + 1) lowerFits
      have tests := frame.testGates_length_le higher.leaves higherDistinct level present
      simp only [gatesAt, List.length_append, List.length_cons, List.length_nil,
        ListPriority.Tree.leaves, ListPriority.Tree.testVolume,
        ListPriority.Tree.forks]
      nlinarith

end Frame

end

end QuantumAlg.EncodedBit.FirstOne
