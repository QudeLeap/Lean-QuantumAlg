/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries

/-!
# Exact full-frame placement of an existing native program

A placement identifies every source bit with one target position. The encoding
compatibility is stated at those same positions, so a semantic basis
permutation cannot be paired with unrelated physical addresses. The placed
program is Core's actual `placeAt` construction: every native or oracle leaf is
relocated and embedded in the complete target frame.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Source Target : Type}

/-- A complete position map whose encoding equation agrees wire by wire. -/
structure FullPlacement (source : BinaryLabelEncoding Source)
    (target : BinaryLabelEncoding Target) where
  grouping : Target ≃ Source
  basis : (Qubits source.width).Index ≃ (Qubits target.width).Index
  basis_encode : ∀ state, basis (source.encode (grouping state)) = target.encode state
  physicalIndex : Nat → Nat
  wire_injective : Function.Injective
    (fun index : Fin source.width => physicalIndex index.val)
  wire_within : ∀ index : Fin source.width, physicalIndex index.val < target.width
  wire_surjective : Function.Surjective
    (fun index : Fin source.width =>
      (⟨physicalIndex index.val, wire_within index⟩ : Fin target.width))
  /-- The semantic basis map reads each source bit at its actual target position. -/
  basis_position : ∀ label index,
    (BinaryBasis.bigEndianEquiv target.width).symm (basis label)
        ⟨physicalIndex index.val, wire_within index⟩ =
      (BinaryBasis.bigEndianEquiv source.width).symm label index

namespace FullPlacement

variable {source : BinaryLabelEncoding Source} {target : BinaryLabelEncoding Target}
variable (layout : FullPlacement source target)
variable {gates : GateModel} {oracles : OracleModel}

private abbrev sourceLayout := (QubitLayout.canonical source.width).toQuantum
private abbrev targetLayout := (QubitLayout.canonical target.width).toQuantum

private def position : Fin source.width ↪ Fin target.width where
  toFun index := ⟨layout.physicalIndex index.val, layout.wire_within index⟩
  inj' := by
    intro left right same
    apply layout.wire_injective
    exact congrArg Fin.val same

private theorem position_surjective : Function.Surjective layout.position :=
  layout.wire_surjective

private theorem dimensions (index : Fin source.width) :
    ((sourceLayout (source := source)).wire index).dimension =
      ((targetLayout (target := target)).wire (layout.position index)).dimension := by
  rfl

/-- Place the supplied actual body at the declared complete target positions. -/
def place (body : UnitaryCircuit gates oracles (sourceLayout (source := source))) :
    UnitaryCircuit gates oracles (targetLayout (target := target)) :=
  UnitaryCircuit.placeAt (sourceLayout (source := source)) (targetLayout (target := target))
    layout.position layout.dimensions body

/-- Reassemble the complete supplied body's action through the actual inverse grouping. -/
def step (action : Source → Source) (state : Target) : Target :=
  layout.grouping.symm (action (layout.grouping state))

private theorem selectedInput_encode (state : Target) :
    UnitaryCircuit.selectedInput (sourceLayout (source := source))
        (targetLayout (target := target)) layout.position layout.dimensions
        ((QubitLayout.canonical target.width).basisEquiv.symm (target.encode state)) =
      (QubitLayout.canonical source.width).basisEquiv.symm
        (source.encode (layout.grouping state)) := by
  funext index
  apply finTwoEquiv.injective
  change
    finTwoEquiv
        ((BinaryBasis.bigEndianEquiv target.width).symm (target.encode state)
          (layout.position index)) =
      finTwoEquiv
        ((BinaryBasis.bigEndianEquiv source.width).symm
          (source.encode (layout.grouping state)) index)
  rw [← layout.basis_encode state]
  exact congrArg finTwoEquiv
    (layout.basis_position (source.encode (layout.grouping state)) index)

private theorem complement_encode (left right : Target) :
    (targetLayout (target := target)).restrictComplementBasis
        (Finset.univ.map layout.position)
        ((QubitLayout.canonical target.width).basisEquiv.symm (target.encode left)) =
      (targetLayout (target := target)).restrictComplementBasis
        (Finset.univ.map layout.position)
        ((QubitLayout.canonical target.width).basisEquiv.symm (target.encode right)) := by
  funext index
  obtain ⟨sourceIndex, same⟩ := layout.position_surjective index.val
  exfalso
  exact (Finset.mem_compl.mp index.property)
    (same ▸ Finset.mem_map_of_mem layout.position (Finset.mem_univ sourceIndex))

/-- Exact encoded-basis semantics follow from the same physical position map. -/
theorem place_realizes {body : UnitaryCircuit gates oracles (sourceLayout (source := source))}
    {action : Source → Source} (realizes : UnitaryCircuit.Realizes source body action) :
    UnitaryCircuit.Realizes target (layout.place body) (layout.step action) where
  apply_encoded_ket := by
    intro state
    refine UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
      (sourceLayout (source := source)) (targetLayout (target := target))
      layout.position layout.dimensions body
      ((QubitLayout.canonical source.width).basisEquiv.symm
        (source.encode (layout.grouping state)))
      ((QubitLayout.canonical source.width).basisEquiv.symm
        (source.encode (action (layout.grouping state))))
      (realizes.apply_encoded_ket (layout.grouping state))
      ((QubitLayout.canonical target.width).basisEquiv.symm (target.encode state))
      ((QubitLayout.canonical target.width).basisEquiv.symm
        (target.encode (layout.step action state))) ?_ ?_ ?_
    · exact layout.selectedInput_encode state
    · simpa only [step, Equiv.apply_symm_apply] using
        layout.selectedInput_encode
          (layout.grouping.symm (action (layout.grouping state)))
    · exact layout.complement_encode (layout.step action state) state

/-- Transport one proved admitted-input equation through the same actual placement. -/
theorem place_ket_of_eq
    (body : UnitaryCircuit gates oracles (sourceLayout (source := source)))
    (initial final : Source)
    (actual : body.applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical source.width).basisEquiv.symm (source.encode initial))) =
        NormalizedVector.ket
          ((QubitLayout.canonical source.width).basisEquiv.symm (source.encode final))) :
    (layout.place body).applyNormalized
      (NormalizedVector.ket
        ((QubitLayout.canonical target.width).basisEquiv.symm
          (target.encode (layout.grouping.symm initial)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical target.width).basisEquiv.symm
          (target.encode (layout.grouping.symm final))) := by
  refine UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    (sourceLayout (source := source)) (targetLayout (target := target))
    layout.position layout.dimensions body
    ((QubitLayout.canonical source.width).basisEquiv.symm (source.encode initial))
    ((QubitLayout.canonical source.width).basisEquiv.symm (source.encode final))
    actual
    ((QubitLayout.canonical target.width).basisEquiv.symm
      (target.encode (layout.grouping.symm initial)))
    ((QubitLayout.canonical target.width).basisEquiv.symm
      (target.encode (layout.grouping.symm final))) ?_ ?_ ?_
  · simpa only [Equiv.apply_symm_apply] using
      layout.selectedInput_encode (layout.grouping.symm initial)
  · simpa only [Equiv.apply_symm_apply] using
      layout.selectedInput_encode (layout.grouping.symm final)
  · exact layout.complement_encode
      (layout.grouping.symm final) (layout.grouping.symm initial)

/-- Placement retains the complete ordered native event trace. -/
theorem place_eventTrace
    (body : UnitaryCircuit gates oracles (sourceLayout (source := source))) :
    (layout.place body).eventTrace = body.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

/-- Placement retains every evaluated native dependency depth. -/
theorem place_evaluatedEventDepth
    (body : UnitaryCircuit gates oracles (sourceLayout (source := source)))
    (duration : Resource.Event (.quantum gates oracles) → Nat) :
    (layout.place body).evaluatedEventDepth duration = body.evaluatedEventDepth duration :=
  UnitaryCircuit.placeAt_evaluatedEventDepth _ _ _ _ _ _

end FullPlacement

end

end QuantumAlg.EncodedBit
