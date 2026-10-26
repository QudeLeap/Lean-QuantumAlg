/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask

/-!
# Joint X propagation through physically independent CNOTs

These are complete encoded-state equalities for arbitrary input values. In
particular they retain every dirty target and every complementary system.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.CnotLayer

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

private lemma target_disjoint (first second : CnotEdge encoding)
    (separate : Disjoint first.support second.support) :
    GateSpec.bitDisjoint first.target second.gate := by
  constructor
  · intro equal
    have own : first.target.wire ∈ first.support := by simp [CnotEdge.support]
    have other : first.target.wire ∈ second.support := by simp [CnotEdge.support, equal]
    exact Finset.disjoint_left.mp separate own other
  · intro equal
    have own : first.target.wire ∈ first.support := by simp [CnotEdge.support]
    have other : first.target.wire ∈ second.support := by simp [CnotEdge.support, equal]
    exact Finset.disjoint_left.mp separate own other

private lemma propagate_edges (edges : List (CnotEdge encoding))
    (separate : edges.Pairwise (fun first second => Disjoint first.support second.support))
    (active : List (EncodedBit encoding)) (distinct : (active.map EncodedBit.wire).Nodup)
    (present : ∀ edge ∈ edges, edge.control.wire ∈ active.map EncodedBit.wire)
    (state : Data) :
    GateSpec.stepList (edges.map CnotEdge.gate) (flipBits active state) =
      flipBits active (flipBits (edges.map CnotEdge.target)
        (GateSpec.stepList (edges.map CnotEdge.gate) state)) := by
  induction edges generalizing state with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨firstSeparate, restSeparate⟩ := List.pairwise_cons.mp separate
      have restDisjoint : ∀ gate ∈ rest.map CnotEdge.gate,
          GateSpec.bitDisjoint first.target gate := by
        intro gate member
        obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp member
        exact target_disjoint first edge (firstSeparate edge edgePresent)
      change GateSpec.stepList (rest.map CnotEdge.gate)
        (cnotStep first.control first.target (flipBits active state)) = _
      rw [cnotStep_flipBits first.control first.target active distinct
        (present first (by simp)),
        GateSpec.stepList_flip_comm_of_bitDisjoint _ first.target restDisjoint,
        ih restSeparate (fun edge member => present edge (by simp [member]))]
      simp only [List.map_cons, GateSpec.stepList, CnotEdge.gate, GateSpec.step,
        flipBits, flipBits_flip]

/-- Each selected control X produces exactly one additional X on its own target. -/
lemma propagates (layer : CnotLayer encoding)
    (active : List (EncodedBit encoding)) (distinct : (active.map EncodedBit.wire).Nodup)
    (present : ∀ edge ∈ layer.edges, edge.control.wire ∈ active.map EncodedBit.wire)
    (state : Data) :
    GateSpec.stepList layer.gates (flipBits active state) =
      flipBits active (flipBits (layer.edges.map CnotEdge.target)
        (GateSpec.stepList layer.gates state)) :=
  propagate_edges layer.edges layer.separate active distinct present state

end

end QuantumAlg.EncodedBit.WindowLookup.CnotLayer
