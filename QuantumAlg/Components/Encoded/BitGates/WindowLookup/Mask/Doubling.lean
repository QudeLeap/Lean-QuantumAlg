/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Propagation

/-!
# Concrete doubling layers on an existing target word

A span of already selected X positions is doubled by one physically independent
CNOT layer. The layer uses only original target wires and works on arbitrary
dirty values. Its width is the number of newly reached target positions.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {count : Nat}

/-- The number of new target wires reached from a positive current span. -/
def doublingSize (count span : Nat) : Nat := min span (count - span)

private def doublingSource (span : Nat) (index : Fin (doublingSize count span)) : Fin count :=
  ⟨index, by have := index.isLt; dsimp [doublingSize] at this; omega⟩

private def doublingTarget (span : Nat) (index : Fin (doublingSize count span)) : Fin count :=
  ⟨span + index, by have := index.isLt; dsimp [doublingSize] at this; omega⟩

/-- One concrete edge copies the X difference to the corresponding new target wire. -/
def doublingEdge (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span) (index : Fin (doublingSize count span)) :
    CnotEdge encoding where
  control := target (doublingSource span index)
  target := target (doublingTarget span index)
  different := by
    intro equal
    have values := congrArg Fin.val (distinct equal)
    dsimp [doublingSource, doublingTarget] at values
    omega

private lemma doubling_support_disjoint (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span)
    (first second : Fin (doublingSize count span)) (different : first ≠ second) :
    Disjoint (doublingEdge target distinct span positive first).support
      (doublingEdge target distinct span positive second).support := by
  apply Finset.disjoint_left.mpr
  intro wire firstPresent secondPresent
  simp only [CnotEdge.support, doublingEdge, Finset.mem_insert, Finset.mem_singleton]
    at firstPresent secondPresent
  have firstBound := first.isLt
  have secondBound := second.isLt
  dsimp [doublingSize] at firstBound secondBound
  rcases firstPresent with firstControl | firstTarget <;>
    rcases secondPresent with secondControl | secondTarget
  · have values := congrArg Fin.val (distinct (firstControl.symm.trans secondControl))
    apply different
    apply Fin.ext
    exact values
  · have values := congrArg Fin.val (distinct (firstControl.symm.trans secondTarget))
    dsimp [doublingSource, doublingTarget] at values
    omega
  · have values := congrArg Fin.val (distinct (firstTarget.symm.trans secondControl))
    dsimp [doublingSource, doublingTarget] at values
    omega
  · have values := congrArg Fin.val (distinct (firstTarget.symm.trans secondTarget))
    dsimp [doublingSource, doublingTarget] at values
    apply different
    apply Fin.ext
    omega

/-- All controls and targets in this actual layer are physically disjoint. -/
def doublingLayer (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span) : CnotLayer encoding where
  edges := List.ofFn (doublingEdge target distinct span positive)
  separate := by
    rw [List.pairwise_ofFn]
    intro first second ordered
    exact doubling_support_disjoint target distinct span positive first second
      (Fin.ne_of_lt ordered)

/-- There is one actual CNOT for each newly reached target. -/
lemma doublingLayer_length (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span) :
    (doublingLayer target distinct span positive).edges.length = doublingSize count span := by
  simp only [doublingLayer, List.length_ofFn]

/-- The current ordered prefix of selected physical target bits. -/
def prefixBits (target : Fin count → EncodedBit encoding) (span : Nat) :
    List (EncodedBit encoding) :=
  List.ofFn fun index : Fin (min span count) =>
    target ⟨index, lt_of_lt_of_le index.isLt (Nat.min_le_right span count)⟩

/-- Original wire injectivity makes every reached prefix duplicate free. -/
lemma prefixBits_distinct (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire)) (span : Nat) :
    ((prefixBits target span).map EncodedBit.wire).Nodup := by
  rw [prefixBits, List.map_ofFn]
  apply List.nodup_ofFn_ofInjective
  intro first second same
  exact Fin.ext (congrArg (fun index : Fin count => index.val) (distinct same))

private lemma doubling_control_present (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span)
    (edge : CnotEdge encoding)
    (member : edge ∈ (doublingLayer target distinct span positive).edges) :
    edge.control.wire ∈ (prefixBits target span).map EncodedBit.wire := by
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  apply List.mem_map.mpr
  have bound := index.isLt
  dsimp [doublingSize] at bound
  refine ⟨target (doublingSource span index), ?_, rfl⟩
  apply List.mem_ofFn.mpr
  refine ⟨⟨index.val, by omega⟩, ?_⟩
  rfl

/-- Appending all newly reached targets produces exactly the doubled original prefix. -/
lemma prefixBits_doubling (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span) :
    prefixBits target span ++
      ((doublingLayer target distinct span positive).edges.map CnotEdge.target) =
        prefixBits target (2 * span) := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_map, doublingLayer_length,
      prefixBits, List.length_ofFn, doublingSize]
    omega
  · intro index leftBound rightBound
    have limits : index < min span count + min span (count - span) := by
      simpa only [List.length_append, List.length_map, doublingLayer_length,
        prefixBits, List.length_ofFn, doublingSize] using leftBound
    by_cases before : index < min span count
    · rw [List.getElem_append_left (by simpa only [prefixBits, List.length_ofFn] using before)]
      simp only [prefixBits, List.getElem_ofFn]
    · rw [List.getElem_append_right
        (by simpa only [prefixBits, List.length_ofFn] using Nat.le_of_not_gt before)]
      simp only [prefixBits, doublingLayer, List.getElem_map, List.getElem_ofFn,
        doublingEdge, doublingTarget, List.length_ofFn]
      congr 1
      apply Fin.ext
      dsimp
      omega

/-- One actual independent layer doubles the complete X difference on arbitrary dirty targets. -/
lemma doublingLayer_propagates (target : Fin count → EncodedBit encoding)
    (distinct : Function.Injective (fun index => (target index).wire))
    (span : Nat) (positive : 0 < span) (state : Data) :
    GateSpec.stepList (doublingLayer target distinct span positive).gates
      (flipBits (prefixBits target span) state) =
      flipBits (prefixBits target (2 * span))
        (GateSpec.stepList (doublingLayer target distinct span positive).gates state) := by
  rw [(doublingLayer target distinct span positive).propagates
    (prefixBits target span) (prefixBits_distinct target distinct span)
    (doubling_control_present target distinct span positive)]
  rw [← flipBits_append]
  rw [flipBits_perm (List.perm_append_comm), prefixBits_doubling]

end

end QuantumAlg.EncodedBit.WindowLookup
