/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Policy
import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree

/-!
# Actual recursive first-one word from a supplied physical native test policy

The original child order, all complete tests and both prefix CNOTs remain
literal native instructions on the unchanged full physical layout.
-/

namespace QuantumAlg.EncodedBit.FirstOne.TestPolicy

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  {frame : Frame encoding count outputWidth depth} (policy : TestPolicy frame)

open _root_.QuantumAlg.EncodedBit.FirstOne.Frame

/-- Every emitted gate names only supplied actual source, output, prefix or arbitrary work wires. -/
def gatesAt : (tree : ListPriority.Tree (Fin count)) → (distinct : tree.leaves.Nodup) →
    (level : Nat) → (fits : level + tree.height ≤ depth) → List (GateSpec encoding)
  | .empty, _, _, _ => []
  | .leaf label, _, level, fits =>
      let current : Fin (depth + 1) := ⟨level, by
        change level + 0 ≤ depth at fits
        omega⟩
      Word.doubleControlledXorConstantGates (frame.stack.bit current) (frame.source.bit label)
        frame.output (leafMask (outputWidth := outputWidth) label)
        (Ne.symm (frame.sourceStack label current))
        (fun output => Ne.symm (frame.outputStack output current))
        (fun output => frame.sourceOutput label output)
  | .fork higher lower, distinct, level, fits =>
      have present : level < depth := by
        change level + (max higher.height lower.height + 1) ≤ depth at fits
        omega
      have higherDistinct : higher.leaves.Nodup := (List.nodup_append.mp distinct).1
      have lowerDistinct : lower.leaves.Nodup := (List.nodup_append.mp distinct).2.1
      have higherFits : level + 1 + higher.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).1
        omega
      have lowerFits : level + 1 + lower.height ≤ depth := by
        have bounded := (ListPriority.Tree.child_heights_le higher lower).2
        omega
      let toggle := policy.gates higher.leaves higherDistinct level present
      let copy := GateSpec.cnot (frame.enableAt level present) (frame.nextAt level present)
        (frame.enable_next_ne level present)
      toggle ++ (gatesAt lower lowerDistinct (level + 1) lowerFits ++
        (copy :: (gatesAt higher higherDistinct (level + 1) higherFits ++
          (toggle ++ [copy]))))

/-- Compile the complete literal recursive native word on the unchanged complete physical layout. -/
def programAt (tree : ListPriority.Tree (Fin count)) (distinct : tree.leaves.Nodup) (level : Nat)
    (fits : level + tree.height ≤ depth) : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (policy.gatesAt tree distinct level fits)

/-- The full actual recursive word has its exact native ordered event trace. -/
lemma policy_programAt_eventTrace (tree : ListPriority.Tree (Fin count))
    (distinct : tree.leaves.Nodup) (level : Nat)
    (fits : level + tree.height ≤ depth) :
    (policy.programAt tree distinct level fits).eventTrace =
      (policy.gatesAt tree distinct level fits).map (GateSpec.event .empty) :=
  GateSpec.programList_eventTrace _ _ _

end

end QuantumAlg.EncodedBit.FirstOne.TestPolicy
