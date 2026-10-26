/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.FirstOne.Tree
import all QuantumAlg.Util.List.PriorityTree.Balanced
import all QuantumAlg.Util.List.PriorityTree.Position

/-!
# Actual balanced first-one encoder with the full original count sentinel

The existing root controls a paid constant sentinel load. The compact
balanced native emitter then selects the first original source one.
The supplied output is arbitrary, all supplied systems already exist,
and no arithmetic truncation is silently treated as a natural position.
-/

namespace QuantumAlg.EncodedBit.FirstOne.Frame

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count outputWidth depth : Nat}
  (frame : Frame encoding count outputWidth depth)

/-- Complete original finite-index order, divided into compact balanced subwords. -/
def priorityTree (count depth : Nat) : ListPriority.Tree (Fin count) :=
  ListPriority.Tree.balanced depth (List.finRange count)

/-- The actual priority source contains every original position once in order. -/
lemma priorityTree_leaves (fits : count ≤ 2 ^ depth) :
    (priorityTree count depth).leaves = List.finRange count :=
  ListPriority.Tree.balanced_leaves depth _ (by simpa only [List.length_finRange] using fits)

/-- Every real source wire is distinct at every native subtree test. -/
lemma priorityTree_distinct (fits : count ≤ 2 ^ depth) :
    (priorityTree count depth).leaves.Nodup := by
  rw [priorityTree_leaves fits]
  exact List.nodup_finRange _

/-- The supplied prefix stack bounds the actual compact tree height. -/
lemma priorityTree_height : (priorityTree count depth).height ≤ depth :=
  ListPriority.Tree.balanced_height_le depth _

/-- Independent first original one position with the original count as zero sentinel. -/
def firstPosition (state : Data) : Nat :=
  ListPriority.Tree.position (fun label => (frame.source.bit label).get state)

/-- Literal paid root-controlled CNOTs load the sentinel into the existing arbitrary output. -/
def sentinelGates : List (GateSpec encoding) :=
  Word.controlledXorConstantGates (frame.stack.bit ⟨0, by omega⟩) frame.output
    (BitVec.ofNat outputWidth count).toFin
    (fun output => Ne.symm (frame.outputStack output _))

/-- Complete actual native encoder: sentinel load followed by the restored balanced emitter. -/
def encoderGates (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth) :
    List (GateSpec encoding) :=
  frame.sentinelGates ++ frame.gatesAt (priorityTree count height)
    (priorityTree_distinct capacity) 0
    (by have bounded := priorityTree_height (count := count) (depth := height); omega)

/-- The actual encoder on the unchanged full physical layout, with no allocation. -/
def encoderProgram (height : Nat) (capacity : count ≤ 2 ^ height) (fits : height ≤ depth) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (frame.encoderGates height capacity fits)

/-- The actual native ordered event trace is exactly the compiled complete encoder list. -/
lemma encoderProgram_eventTrace (height : Nat) (capacity : count ≤ 2 ^ height)
    (fits : height ≤ depth) :
    (frame.encoderProgram height capacity fits).eventTrace =
      (frame.encoderGates height capacity fits).map (GateSpec.event .empty) :=
  GateSpec.programList_eventTrace _ _ _

end

end QuantumAlg.EncodedBit.FirstOne.Frame
