/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Exact full-frame placement of an existing native program

A placement supplies the actual invertible field grouping, its compatible
full binary basis map, and the distinct original physical wire addresses.
An existing native body is transported through these maps and retains the
complete target frame. The input body still supplies every emitted event
and its own semantic realization; no operation is synthesized from a
semantic action and no new primitive or cost witness is introduced.

Concrete owners establish their grouping and individual wire coordinates.
This owner proves the common normalized-basis transport and preservation
of the body's actual event trace and evaluated depth.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Source Target : Type}

/-- Actual complete field grouping, compatible encoded labels, and physical wire placement. -/
structure FullPlacement (source : BinaryLabelEncoding Source)
    (target : BinaryLabelEncoding Target) where
  grouping : Target ≃ Source
  basis : (Qubits source.width).Index ≃ (Qubits target.width).Index
  basis_encode : ∀ state, basis (source.encode (grouping state)) = target.encode state
  physicalIndex : Nat → Nat
  wire_injective : Function.Injective (fun index : Fin source.width => physicalIndex index.val)
  wire_within : ∀ index : Fin source.width, physicalIndex index.val < target.width

namespace FullPlacement

variable {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
variable (layout : FullPlacement source target)

private def raw (body : UnitaryCircuit (Qubits source.width)) :
    UnitaryCircuit (Qubits target.width) :=
  UnitaryCircuit.reindex layout.basis body

private theorem mapped_nodup (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    ((layout.raw body).physical_idx.map layout.physicalIndex).Nodup := by
  apply List.Nodup.map_on _ (layout.raw body).physical_idx_nodup
  intro left leftPresent right rightPresent same
  have leftBound := List.mem_range.mp (within leftPresent)
  have rightBound := List.mem_range.mp (within rightPresent)
  exact congrArg (fun index : Fin source.width => index.val)
    (layout.wire_injective
      (a₁ := ⟨left, leftBound⟩) (a₂ := ⟨right, rightBound⟩) same)

private def addressed (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    UnitaryCircuit (Qubits target.width) :=
  UnitaryCircuit.relabel (layout.raw body)
    { toFun := layout.physicalIndex
      map_layout := rfl
      old_nodup := (layout.raw body).physical_idx_nodup
      new_nodup := layout.mapped_nodup body within }

private theorem addressed_range (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    (layout.addressed body within).physical_idx ⊆ List.range target.width := by
  intro wire present
  change wire ∈ (layout.raw body).physical_idx.map layout.physicalIndex at present
  rcases List.mem_map.mp present with ⟨old, oldPresent, rfl⟩
  exact List.mem_range.mpr (layout.wire_within
    ⟨old, List.mem_range.mp (within oldPresent)⟩)

/-- Place the supplied actual native body and retain every original target-frame wire. -/
def place (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    UnitaryCircuit (Qubits target.width) :=
  (layout.addressed body within).seq
    (UnitaryCircuit.identity (Qubits target.width) (List.range target.width) List.nodup_range)

/-- Reassemble the complete supplied body's action through the actual inverse grouping. -/
def step (action : Source → Source) (state : Target) : Target :=
  layout.grouping.symm (action (layout.grouping state))

/-- Exact actual basis amplitudes are transported through the compatible real field encodings. -/
theorem place_realizes {body : UnitaryCircuit (Qubits source.width)} {action : Source → Source}
    (within : body.physical_idx ⊆ List.range source.width)
    (realizes : UnitaryCircuit.Realizes source body action) :
    UnitaryCircuit.Realizes target (layout.place body within) (layout.step action) where
  apply_encoded_ket := by
    intro state
    have actual := realizes.apply_encoded_ket (layout.grouping state)
    have transported := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits source.width) (S := Qubits target.width) layout.basis body _ _ actual
    have output : action (layout.grouping state) =
        layout.grouping (layout.step action state) :=
      (layout.grouping.apply_symm_apply _).symm
    rw [output] at transported
    have inputKet := congrArg
      (fun label : (Qubits target.width).Index =>
        NormalizedVector.ket (R := Qubits target.width) label)
      (layout.basis_encode state)
    have outputKet := congrArg
      (fun label : (Qubits target.width).Index =>
        NormalizedVector.ket (R := Qubits target.width) label)
      (layout.basis_encode (layout.step action state))
    have encodedRun := (congrArg (layout.raw body).applyNormalized inputKet.symm).trans
      (transported.trans outputKet)
    unfold place
    rw [UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity]
    unfold addressed
    rw [UnitaryCircuit.Realizes.applyNormalized_relabel]
    exact encodedRun

/-- The placed program's actual declared footprint is the complete original target frame. -/
theorem place_physical (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    (layout.place body within).physical_idx = List.range target.width := by
  change UnitaryCircuit.unionPhysicalIdx (layout.addressed body within).physical_idx
    (List.range target.width) = _
  exact UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _
    (layout.addressed_range body within)

/-- Every actual body event is retained in its original order. -/
theorem place_eventTrace (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width) :
    (layout.place body within).eventTrace = body.eventTrace := by
  have empty : (UnitaryCircuit.identity (Qubits target.width)
      (List.range target.width) List.nodup_range).eventTrace = [] := rfl
  rw [place, UnitaryCircuit.seq_eventTrace, empty, List.append_nil, addressed,
    UnitaryCircuit.relabel_eventTrace, raw]
  exact UnitaryCircuit.reindex_eventTrace layout.basis body

/-- Every actual native duration assignment has the same evaluated execution depth. -/
theorem place_evaluatedEventDepth (body : UnitaryCircuit (Qubits source.width))
    (within : body.physical_idx ⊆ List.range source.width)
    (duration : Resource.Event .quantum → Nat) :
    (layout.place body within).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  rw [place, UnitaryCircuit.evaluatedEventDepth_seq]
  change (layout.addressed body within).evaluatedEventDepth duration + 0 = _
  rw [Nat.add_zero, addressed, UnitaryCircuit.evaluatedEventDepth_relabel]
  simp only [UnitaryCircuit.evaluatedEventDepth, raw, UnitaryCircuit.reindex_eventDepth]

end FullPlacement

end

end QuantumAlg.EncodedBit
