/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Mask.Network
import all QuantumAlg.Components.Encoded.BitGates.Small.Phase

/-!
# Physical parity fan-in for masked phases

Reversing each CNOT direction and the layer order turns the original target
fanout into a parity fan-in. All supports remain physically disjoint inside
each layer. The construction uses the original target systems, including
the arbitrary dirty values that must be restored after the actual phase.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- XOR of actual target readouts in a static physical mask. -/
def bitParity : List (EncodedBit encoding) → Data → Bool
  | [], _ => false
  | bit :: rest, state => bit.get state ^^ bitParity rest state

/-- Splitting the static mask splits its actual readout parity. -/
lemma bitParity_append (first second : List (EncodedBit encoding)) (state : Data) :
    bitParity (first ++ second) state = (bitParity first state ^^ bitParity second state) := by
  induction first with
  | nil => exact (Bool.false_xor _).symm
  | cons bit rest ih =>
      change (bit.get state ^^ bitParity (rest ++ second) state) =
        ((bit.get state ^^ bitParity rest state) ^^ bitParity second state)
      rw [ih, Bool.xor_assoc]

/-- Equality of each physical readout is sufficient for equality of the full mask parity. -/
lemma bitParity_congr (bits : List (EncodedBit encoding)) (first second : Data)
    (same : ∀ bit ∈ bits, bit.get first = bit.get second) :
    bitParity bits first = bitParity bits second := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      change (bit.get first ^^ bitParity rest first) = _
      rw [same bit (by simp), ih (fun other member => same other (by simp [member]))]
      rfl

private lemma get_wire_eq (first second : EncodedBit encoding)
    (same : first.wire = second.wire) (state : Data) : first.get state = second.get state := by
  rw [← first.get_eq, ← second.get_eq, same]

private lemma bitParity_cnot_unchanged (bits : List (EncodedBit encoding))
    (control target : EncodedBit encoding)
    (outside : ∀ bit ∈ bits, target.wire ≠ bit.wire) (state : Data) :
    bitParity bits (cnotStep control target state) = bitParity bits state :=
  bitParity_congr bits _ _ fun bit member =>
    cnotStep_get_of_target_ne control target bit (outside bit member) state

/-- Toggling one present target adds the original control readout exactly once. -/
lemma bitParity_cnot (bits : List (EncodedBit encoding))
    (distinct : (bits.map EncodedBit.wire).Nodup)
    (control target : EncodedBit encoding)
    (present : target.wire ∈ bits.map EncodedBit.wire) (state : Data) :
    bitParity bits (cnotStep control target state) =
      (bitParity bits state ^^ control.get state) := by
  induction bits with
  | nil => simp at present
  | cons first rest ih =>
      obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp distinct
      by_cases same : first.wire = target.wire
      · have outside : ∀ bit ∈ rest, target.wire ≠ bit.wire := by
          intro bit member equal
          apply absent
          exact List.mem_map.mpr ⟨bit, member, equal.symm.trans same.symm⟩
        change (first.get (cnotStep control target state) ^^
          bitParity rest (cnotStep control target state)) =
          ((first.get state ^^ bitParity rest state) ^^ control.get state)
        rw [get_wire_eq first target same, cnotStep_get_target,
          bitParity_cnot_unchanged rest control target outside,
          get_wire_eq first target same]
        cases target.get state <;> cases bitParity rest state <;> cases control.get state <;> rfl
      · have tailPresent : target.wire ∈ rest.map EncodedBit.wire :=
          (List.mem_cons.mp present).resolve_left (Ne.symm same)
        change (first.get (cnotStep control target state) ^^
          bitParity rest (cnotStep control target state)) =
          ((first.get state ^^ bitParity rest state) ^^ control.get state)
        rw [cnotStep_get_of_target_ne control target first (Ne.symm same),
          ih restDistinct tailPresent]
        exact (Bool.xor_assoc _ _ _).symm

namespace CnotEdge

/-- Exchange the two existing physical endpoints of one native CNOT. -/
def transpose (edge : CnotEdge encoding) : CnotEdge encoding where
  control := edge.target
  target := edge.control
  different := edge.different.symm

/-- Reversing CNOT direction retains the complete physical support. -/
lemma transpose_support (edge : CnotEdge encoding) : edge.transpose.support = edge.support := by
  exact Finset.pair_comm _ _

end CnotEdge

namespace CnotLayer

/-- Transpose all native CNOTs while retaining certified physical parallel independence. -/
def transpose (layer : CnotLayer encoding) : CnotLayer encoding where
  edges := layer.edges.map CnotEdge.transpose
  separate := by
    apply List.pairwise_map.mpr
    apply layer.separate.imp
    intro first second disjoint
    simpa only [CnotEdge.transpose_support] using disjoint

private lemma source_other_target (first second : CnotEdge encoding)
    (disjoint : Disjoint first.support second.support) :
    first.control.wire ≠ second.target.wire := by
  intro same
  have own : first.control.wire ∈ first.support := by simp [CnotEdge.support]
  have other : first.control.wire ∈ second.support := by simp [CnotEdge.support, same]
  exact Finset.disjoint_left.mp disjoint own other

private lemma transpose_parity_edges (edges : List (CnotEdge encoding))
    (separate : edges.Pairwise (fun first second => Disjoint first.support second.support))
    (active : List (EncodedBit encoding)) (distinct : (active.map EncodedBit.wire).Nodup)
    (present : ∀ edge ∈ edges, edge.control.wire ∈ active.map EncodedBit.wire)
    (state : Data) :
    bitParity active (GateSpec.stepList (edges.map fun edge => edge.transpose.gate) state) =
      (bitParity active state ^^ bitParity (edges.map CnotEdge.target) state) := by
  induction edges generalizing state with
  | nil => exact (Bool.xor_false _).symm
  | cons first rest ih =>
      obtain ⟨firstSeparate, restSeparate⟩ := List.pairwise_cons.mp separate
      change bitParity active (GateSpec.stepList (rest.map fun edge => edge.transpose.gate)
        (cnotStep first.target first.control state)) = _
      rw [ih restSeparate (fun edge member => present edge (by simp [member])),
        bitParity_cnot active distinct first.target first.control (present first (by simp)),
        bitParity_cnot_unchanged (rest.map CnotEdge.target) first.target first.control
          (by
            intro bit member
            obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp member
            exact source_other_target first edge (firstSeparate edge edgePresent))]
      exact Bool.xor_assoc _ _ _

/-- The transposed actual layer extends a parity mask to its newly reached target positions. -/
lemma transpose_parity (layer : CnotLayer encoding)
    (active : List (EncodedBit encoding)) (distinct : (active.map EncodedBit.wire).Nodup)
    (present : ∀ edge ∈ layer.edges, edge.control.wire ∈ active.map EncodedBit.wire)
    (state : Data) :
    bitParity active (GateSpec.stepList layer.transpose.gates state) =
      bitParity (active ++ layer.edges.map CnotEdge.target) state := by
  rw [bitParity_append]
  simpa only [transpose, gates, List.map_map, Function.comp_def] using
    transpose_parity_edges layer.edges layer.separate active distinct present state

end CnotLayer

/-- The actual fan-in reverses target propagation order and exchanges each CNOT direction. -/
def parityFanInWord (layers : List (CnotLayer encoding)) : List (CnotLayer encoding) :=
  layers.reverse.map CnotLayer.transpose

/-- Physical parity fan-in needs exactly the original number of independent layers. -/
lemma parityFanInWord_length (layers : List (CnotLayer encoding)) :
    (parityFanInWord layers).length = layers.length := by
  simp only [parityFanInWord, List.length_map, List.length_reverse]

end

end QuantumAlg.EncodedBit.WindowLookup
