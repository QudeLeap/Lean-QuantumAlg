/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.PreparedFrame
import all QuantumAlg.Core.Base.Layout.Quantum.IdentityPosition
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Physical placement of initial shared-EEA arithmetic beside the input

Every canonical native address is located by the matching physical identity
in the actual post-preparation context. The selected-model program retains
the original native matrix and event list on those physical wires.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InputRuntimePlacement

noncomputable section

open Execution InputPreparation

private def source (width : Nat) : QuantumLayout (encoding width).width :=
  (QubitLayout.canonical (encoding width).width).toQuantum

private theorem source_contained (width : Nat) :
    (source width).identities ⊆ (after width).quantumLayout.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (QubitLayout.canonical (encoding width).width).systemIdx ⊆
    (after width).physicalIdx
  rw [QubitLayout.canonical_systemIdx]
  exact range_contained width

/-- The canonical source address selects the same identity in the live context. -/
def position (width : Nat) :
    Fin (encoding width).width ↪ Fin (after width).systemCount :=
  QuantumLayout.positionOfIdentity (source width) (after width).quantumLayout
    (source_contained width)

theorem position_identity (width : Nat) (index : Fin (encoding width).width) :
    ((after width).quantumLayout.wire (position width index)).identity = index.val := by
  exact QuantumLayout.positionOfIdentity_identity (source width)
    (after width).quantumLayout (source_contained width) index

private theorem before_count (width : Nat) : (before width).systemCount = width := by
  change ((inputLayout width).wires ++ []).length = width
  simp

private theorem after_count (width : Nat) :
    (after width).systemCount = auxiliaryWidth width + width := by
  change ((auxiliaryLayout width).wires ++ (before width).quantumWires).length = _
  rw [List.length_append, QuantumLayout.wires_length]
  exact congrArg (auxiliaryWidth width + ·) (before_count width)

/-- The physical identity map covers the complete live input frame. -/
theorem position_surjective (width : Nat) : Function.Surjective (position width) := by
  have sameCount : (encoding width).width = (after width).systemCount := by
    rw [after_count]
    have complete := complete_width width
    omega
  let endomap := fun index : Fin (encoding width).width =>
    Fin.cast sameCount.symm (position width index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply (position width).injective
    exact Fin.cast_injective sameCount.symm same
  intro target
  obtain ⟨selected, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameCount.symm target)
  exact ⟨selected, Fin.cast_injective sameCount.symm same⟩

private theorem before_wires (width : Nat) :
    (inputLayout width).wires = (before width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width).wires = (inputLayout width).wires ++ []
  exact (List.append_nil _).symm

private def oldPosition (width : Nat) : Fin width ≃ Fin (before width).systemCount :=
  positionsOfEqualWires (inputLayout width) (before width).quantumLayout
    (before_wires width)

private theorem oldPosition_identity (width : Nat) (index : Fin width) :
    ((before width).quantumLayout.wire (oldPosition width index)).identity =
      prefixWidth width + index.val := by
  have same := wireAtCorrespondingPosition (inputLayout width)
    (before width).quantumLayout (before_wires width) index
  exact congrArg QuantumWire.identity same

/-- A source auxiliary position selects the actual freshly allocated wire. -/
theorem position_auxiliary (width : Nat) (index : Fin (auxiliaryWidth width)) :
    position width (InputAssembly.auxiliaryPosition width index) =
      PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
        (.inl index) := by
  apply (after width).quantumLayout.identityInjective
  change ((after width).quantumLayout.wire
      (position width (InputAssembly.auxiliaryPosition width index))).identity =
    ((after width).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
        (.inl index))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_new_wire (before width)
    auxiliaryKey (auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) index
  exact (congrArg QuantumWire.identity same).symm

/-- A source input position selects the same previously supplied physical wire. -/
theorem position_input (width : Nat) (index : Fin width) :
    position width (InputAssembly.inputPosition width index) =
      PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
        (.inr (oldPosition width index)) := by
  apply (after width).quantumLayout.identityInjective
  change ((after width).quantumLayout.wire
      (position width (InputAssembly.inputPosition width index))).identity =
    ((after width).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
        (.inr (oldPosition width index)))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_old_wire (before width)
    auxiliaryKey (auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) (oldPosition width index)
  exact (oldPosition_identity width index).symm.trans
    (congrArg QuantumWire.identity same).symm

private theorem after_dimension (width : Nat) (index : Fin (after width).systemCount) :
    ((after width).quantumLayout.wire index).dimension = 2 := by
  have member : ((after width).quantumLayout.wire index) ∈
      (after width).quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  change ((after width).quantumLayout.wire index) ∈
    (auxiliaryLayout width).wires ++ (before width).quantumWires at member
  rcases List.mem_append.mp member with fresh | old
  · change ((after width).quantumLayout.wire index) ∈
      (auxiliaryQubitLayout width).toQuantumLayout.wires at fresh
    obtain ⟨located, same⟩ := List.mem_ofFn.mp fresh
    rw [← same]
    rfl
  · change ((after width).quantumLayout.wire index) ∈
      (inputLayout width).wires ++ [] at old
    have input := (List.mem_append.mp old).resolve_right (by simp)
    change ((after width).quantumLayout.wire index) ∈
      (inputQubitLayout width).toQuantumLayout.wires at input
    obtain ⟨located, same⟩ := List.mem_ofFn.mp input
    rw [← same]
    rfl

theorem position_dimensions (width : Nat) (index : Fin (encoding width).width) :
    ((source width).wire index).dimension =
      ((after width).quantumLayout.wire (position width index)).dimension := by
  rw [after_dimension]
  rfl

/-- The placed source reads each fresh auxiliary coordinate without relabeling it. -/
theorem selected_auxiliary (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin (auxiliaryWidth width)) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InputAssembly.assembly width (fresh, old))
      (InputAssembly.auxiliaryPosition width index)).val = (fresh index).val := by
  change (InputAssembly.assembly width (fresh, old)
    (position width (InputAssembly.auxiliaryPosition width index))).val = _
  rw [position_auxiliary]
  exact preparedLocalBasisEquiv_new_value (before width) auxiliaryKey
    (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
    fresh old index

/-- The placed source reads every unchanged original input coordinate. -/
theorem selected_input (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin width) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InputAssembly.assembly width (fresh, old))
      (InputAssembly.inputPosition width index)).val =
        (old (oldPosition width index)).val := by
  change (InputAssembly.assembly width (fresh, old)
    (position width (InputAssembly.inputPosition width index))).val = _
  rw [position_input]
  exact preparedLocalBasisEquiv_old_value (before width) auxiliaryKey
    (auxiliaryLayout width) (auxiliary_fresh width) (auxiliary_disjoint width)
    fresh old (oldPosition width index)

private theorem old_value_bit (width : Nat)
    (old : (before width).register.Index) (index : Fin width) :
    (old (oldPosition width index)).val =
      (finTwoEquiv.symm ((inputBasisEquiv width old).val.testBit index.rev.val)).val := by
  let raw := (basisOfEqualWires (inputLayout width) (before width).quantumLayout
    (before_wires width)).symm old
  have stored := basisOfEqualWires_value (inputLayout width)
    (before width).quantumLayout (before_wires width) raw index
  change ((basisOfEqualWires (inputLayout width) (before width).quantumLayout
    (before_wires width))
      ((basisOfEqualWires (inputLayout width) (before width).quantumLayout
        (before_wires width)).symm old) (oldPosition width index)).val =
      (raw index).val at stored
  rw [Equiv.apply_symm_apply] at stored
  have bit : (inputBasisEquiv width old).val.testBit index.rev.val =
      finTwoEquiv (raw index) :=
    (inputQubitLayout width).binaryIndexEquiv_bit raw index
  rw [bit]
  exact stored.trans (congrArg (fun value : Fin 2 => value.val)
    (finTwoEquiv.symm_apply_apply (raw index))).symm

/-- Read the physically selected source cells as their ordinary binary label. -/
def selectedWord (width : Nat) (basis : (after width).register.Index) :
    Fin (2 ^ (encoding width).width) :=
  (QubitLayout.canonical (encoding width).width).basisEquiv
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width) basis)

private theorem selectedWord_bit (width : Nat) (basis : (after width).register.Index)
    (index : Fin (encoding width).width) :
    (selectedWord width basis).val.testBit index.rev.val =
      finTwoEquiv (UnitaryCircuit.selectedInput (source width)
        (after width).quantumLayout (position width) (position_dimensions width)
        basis index) :=
  BinaryBasis.bigEndianEquiv_bit _ _ index

/-- Physical position selection agrees with the independently assembled source label
for every auxiliary value and every original input, including dirty inputs. -/
theorem selectedWord_assembly (width : Nat)
    (fresh : (auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) :
    selectedWord width (InputAssembly.assembly width (fresh, old)) =
      InputAssembly.basisEquiv width (InputAssembly.assembly width (fresh, old)) := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  let wire : Fin (encoding width).width := bit.rev
  have undo : wire.rev = bit := Fin.rev_rev _
  rw [← undo]
  by_cases beforeInput : wire.val < prefixWidth width
  · let auxiliary : Fin (auxiliaryWidth width) := ⟨wire.val, by
      unfold auxiliaryWidth
      omega⟩
    have located : InputAssembly.auxiliaryPosition width auxiliary = wire := by
      apply Fin.ext
      change (if wire.val < prefixWidth width then wire.val else width + wire.val) = wire.val
      rw [if_pos beforeInput]
    rw [← located, selectedWord_bit, InputAssembly.basisEquiv_auxiliary]
    exact congrArg finTwoEquiv
      (Fin.ext (selected_auxiliary width fresh old auxiliary))
  · by_cases inInput : wire.val < prefixWidth width + width
    · let input : Fin width := ⟨wire.val - prefixWidth width, by omega⟩
      have located : InputAssembly.inputPosition width input = wire := by
        apply Fin.ext
        change prefixWidth width + (wire.val - prefixWidth width) = wire.val
        omega
      rw [← located, selectedWord_bit, InputAssembly.basisEquiv_input]
      have same :
          (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
            (position width) (position_dimensions width)
            (InputAssembly.assembly width (fresh, old))
            (InputAssembly.inputPosition width input)) =
            finTwoEquiv.symm ((inputBasisEquiv width old).val.testBit input.rev.val) := by
        apply Fin.ext
        exact (selected_input width fresh old input).trans (old_value_bit width old input)
      rw [same, finTwoEquiv.apply_symm_apply]
    · let auxiliary : Fin (auxiliaryWidth width) := ⟨wire.val - width, by
        have bound := wire.isLt
        have complete := complete_width width
        omega⟩
      have located : InputAssembly.auxiliaryPosition width auxiliary = wire := by
        apply Fin.ext
        change (if wire.val - width < prefixWidth width then wire.val - width
          else width + (wire.val - width)) = wire.val
        rw [if_neg (by omega)]
        omega
      rw [← located, selectedWord_bit, InputAssembly.basisEquiv_auxiliary]
      exact congrArg finTwoEquiv
        (Fin.ext (selected_auxiliary width fresh old auxiliary))

theorem selectedWord_eq_basisEquiv (width : Nat)
    (basis : (after width).register.Index) :
    selectedWord width basis = InputAssembly.basisEquiv width basis := by
  let pair := (InputAssembly.assembly width).symm basis
  have assembled : InputAssembly.assembly width pair = basis :=
    (InputAssembly.assembly width).apply_symm_apply basis
  rw [← assembled]
  exact selectedWord_assembly width pair.1 pair.2

theorem selectedBasis_eq_basisEquiv (width : Nat)
    (basis : (after width).register.Index) :
    UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width) basis =
        (QubitLayout.canonical (encoding width).width).basisEquiv.symm
          (InputAssembly.basisEquiv width basis) := by
  apply (QubitLayout.canonical (encoding width).width).basisEquiv.injective
  exact (selectedWord_eq_basisEquiv width basis).trans
    ((QubitLayout.canonical (encoding width).width).basisEquiv.apply_symm_apply _).symm

/-- Place the complete actual native word at the matching live physical identities. -/
def program (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    UnitaryCircuit AlgorithmGate.model .empty (after width).quantumLayout :=
  UnitaryCircuit.placeAt (source width) (after width).quantumLayout
    (position width) (position_dimensions width) body

theorem program_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    (program width body).eventTrace = body.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

theorem program_eventCost (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    (program width body).eventCost = body.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- A complete native basis action remains exact after its identity-derived placement. -/
theorem program_apply_ket (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width))
    (input output : (source width).Basis)
    (actual : body.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (targetInput targetOutput : (after width).register.Index)
    (inputSelected : UnitaryCircuit.selectedInput (source width)
      (after width).quantumLayout (position width) (position_dimensions width)
      targetInput = input)
    (outputSelected : UnitaryCircuit.selectedInput (source width)
      (after width).quantumLayout (position width) (position_dimensions width)
      targetOutput = output) :
    (program width body).applyNormalized (NormalizedVector.ket targetInput) =
      NormalizedVector.ket targetOutput := by
  apply UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    (source width) (after width).quantumLayout (position width)
    (position_dimensions width) body input output actual targetInput targetOutput
    inputSelected outputSelected
  funext index
  obtain ⟨sourceIndex, same⟩ := position_surjective width index.val
  have absent : index.val ∈ Finset.univ.map (position width) := by
    rw [← same]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ sourceIndex)
  exact False.elim ((Finset.mem_compl.mp index.property) absent)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InputRuntimePlacement
