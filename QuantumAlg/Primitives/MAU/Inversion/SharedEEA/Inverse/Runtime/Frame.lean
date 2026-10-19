/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Assembly
import all QuantumAlg.Core.Base.Layout.Quantum.IdentityPosition
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual runtime placement on the complete two-word shared frame

The runtime context stores auxiliary wires followed by the two supplied
words. The native gate addresses retain their original physical values,
which are all proved to occur in that exact context list. The adapter uses
the unique matching physical identity in the complete live layout; it does
not relabel physical wires or introduce a footprint-completing instruction.

Any actual native program on the same full frame can use this placement,
including the forward and reused inverse in measured division
[LYL+26, sec_point_add/sec_point_add.tex:51-79]. Its native trace and pool are
unchanged. The `Circuit.unitary` constructor remains the single execution
instruction, acting jointly with an arbitrary external reference.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntimeFrame

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

variable {runtimeEnvironment :
  (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution InversePreparation

/-- Runtime order is exactly fresh auxiliary wires followed by the unchanged two supplied words. -/
lemma after_physical (width : Nat) :
    (after width).physicalIdx =
      (InputPreparation.auxiliaryLayout width).identities ++ (inputLayout width).identities := by
  change ((InputPreparation.auxiliaryLayout width).wires ++ (before width).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (InputPreparation.auxiliaryLayout width).identities ++ (before width).physicalIdx = _
  rw [InversePreparation.before_physical]

private lemma input_subset (width : Nat) :
    (InputPreparation.inputLayout width).identities ⊆ (inputLayout width).identities := by
  intro wire present
  change wire ∈ List.ofFn (fun index : Fin width =>
    InputPreparation.prefixWidth width + index.val) at present
  obtain ⟨index, position⟩ := List.mem_ofFn.mp present
  change wire ∈ List.ofFn (fun index : Fin (width + width) => physicalIndex width index.val)
  refine List.mem_ofFn.mpr ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  change (if index.val < width then InputPreparation.prefixWidth width + index.val
    else (encoding width).width + (index.val - width)) = wire
  rw [if_pos index.isLt]
  exact position

private lemma original_subset (width : Nat) :
    (InputPreparation.after width).physicalIdx ⊆ (after width).physicalIdx := by
  intro wire present
  rw [InputPreparation.after_physical] at present
  rw [after_physical]
  rcases List.mem_append.mp present with auxiliary | input
  · exact List.mem_append.mpr (Or.inl auxiliary)
  · exact List.mem_append.mpr (Or.inr (input_subset width input))

/-- Every native address belongs to the real context, including the supplied rightmost word. -/
lemma range_contained (width : Nat) :
    List.range (OutputCopy.encoding width).width ⊆ (after width).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  change wire < (encoding width).width + width at bound
  by_cases original : wire < (encoding width).width
  · exact original_subset width (InputPreparation.range_contained width
      (List.mem_range.mpr original))
  · rw [after_physical]
    apply List.mem_append.mpr
    right
    change wire ∈ List.ofFn (fun index : Fin (width + width) => physicalIndex width index.val)
    let index : Fin (width + width) :=
      ⟨width + (wire - (encoding width).width), by omega⟩
    refine List.mem_ofFn.mpr ⟨index, ?_⟩
    change (if width + (wire - (encoding width).width) < width then _
      else (encoding width).width + (width + (wire - (encoding width).width) - width)) = wire
    rw [if_neg (by omega)]
    omega

/-- The source native word retains its original physical addresses. -/
def source (width : Nat) : QuantumLayout (OutputCopy.encoding width).width :=
  (QubitLayout.canonical (OutputCopy.encoding width).width).toQuantum

private lemma source_contained (width : Nat) :
    (source width).identities ⊆ (after width).quantumLayout.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (QubitLayout.canonical (OutputCopy.encoding width).width).systemIdx ⊆
    (after width).physicalIdx
  rw [QubitLayout.canonical_systemIdx]
  exact range_contained width

/-- Each native address selects the live wire bearing that same physical identity. -/
def position (width : Nat) :
    Fin (OutputCopy.encoding width).width ↪ Fin (after width).systemCount :=
  QuantumLayout.positionOfIdentity (source width) (after width).quantumLayout
    (source_contained width)

lemma position_identity (width : Nat) (index : Fin (OutputCopy.encoding width).width) :
    ((after width).quantumLayout.wire (position width index)).identity = index.val :=
  QuantumLayout.positionOfIdentity_identity (source width)
    (after width).quantumLayout (source_contained width) index

private lemma before_count (width : Nat) : (before width).systemCount = width + width := by
  change ((inputLayout width).wires ++ []).length = width + width
  simp

private lemma after_count (width : Nat) :
    (after width).systemCount = InputPreparation.auxiliaryWidth width + (width + width) := by
  change ((InputPreparation.auxiliaryLayout width).wires ++
    (before width).quantumWires).length = _
  rw [List.length_append, QuantumLayout.wires_length]
  exact congrArg (InputPreparation.auxiliaryWidth width + ·) (before_count width)

/-- The selected native positions cover the complete live two-word frame. -/
lemma position_surjective (width : Nat) : Function.Surjective (position width) := by
  have sameCount : (OutputCopy.encoding width).width = (after width).systemCount := by
    rw [after_count]
    have total := InversePreparation.total_width width
    omega
  let endomap := fun index : Fin (OutputCopy.encoding width).width =>
    Fin.cast sameCount.symm (position width index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply (position width).injective
    exact Fin.cast_injective sameCount.symm same
  intro target
  obtain ⟨selected, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameCount.symm target)
  exact ⟨selected, Fin.cast_injective sameCount.symm same⟩

private lemma after_dimension (width : Nat) (index : Fin (after width).systemCount) :
    ((after width).quantumLayout.wire index).dimension = 2 := by
  have member : ((after width).quantumLayout.wire index) ∈
      (after width).quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  change ((after width).quantumLayout.wire index) ∈
    (InputPreparation.auxiliaryLayout width).wires ++ (before width).quantumWires
      at member
  rcases List.mem_append.mp member with fresh | old
  · change ((after width).quantumLayout.wire index) ∈
      (InputPreparation.auxiliaryQubitLayout width).toQuantumLayout.wires at fresh
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

lemma position_dimensions (width : Nat) (index : Fin (OutputCopy.encoding width).width) :
    ((source width).wire index).dimension =
      ((after width).quantumLayout.wire (position width index)).dimension := by
  rw [after_dimension]
  rfl

private lemma before_wires (width : Nat) :
    (inputLayout width).wires = (before width).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width).wires = (inputLayout width).wires ++ []
  exact (List.append_nil _).symm

private def oldPosition (width : Nat) :
    Fin (width + width) ≃ Fin (before width).systemCount :=
  positionsOfEqualWires (inputLayout width) (before width).quantumLayout
    (before_wires width)

private lemma oldPosition_identity (width : Nat) (index : Fin (width + width)) :
    ((before width).quantumLayout.wire (oldPosition width index)).identity =
      physicalIndex width index.val := by
  have same := wireAtCorrespondingPosition (inputLayout width)
    (before width).quantumLayout (before_wires width) index
  exact congrArg QuantumWire.identity same

private def oldSourcePosition (width : Nat) (index : Fin (width + width)) :
    Fin (OutputCopy.encoding width).width :=
  ⟨physicalIndex width index.val, by
    have bounded := index.isLt
    have complete := InputPreparation.complete_width width
    unfold InputPreparation.auxiliaryWidth at complete
    change physicalIndex width index.val < (encoding width).width + width
    unfold physicalIndex
    split <;> omega⟩

/-- Fresh auxiliary positions select precisely the allocated physical bank. -/
lemma position_auxiliary (width : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    position width (InverseAssembly.auxiliaryPosition width index) =
      PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
        (auxiliary_disjoint width) (.inl index) := by
  apply (after width).quantumLayout.identityInjective
  change ((after width).quantumLayout.wire
      (position width (InverseAssembly.auxiliaryPosition width index))).identity =
    ((after width).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
        (auxiliary_disjoint width) (.inl index))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_new_wire (before width)
    auxiliaryKey (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) index
  exact (congrArg QuantumWire.identity same).symm

/-- Both originally supplied words retain their original physical identities. -/
lemma position_old (width : Nat) (index : Fin (width + width)) :
    position width (oldSourcePosition width index) =
      PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
        (auxiliary_disjoint width) (.inr (oldPosition width index)) := by
  apply (after width).quantumLayout.identityInjective
  change ((after width).quantumLayout.wire
      (position width (oldSourcePosition width index))).identity =
    ((after width).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
        (auxiliary_disjoint width) (.inr (oldPosition width index)))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_old_wire (before width)
    auxiliaryKey (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) (oldPosition width index)
  exact (oldPosition_identity width index).symm.trans
    (congrArg QuantumWire.identity same).symm

/-- Every fresh source bit reads its actual prepared auxiliary value. -/
lemma selected_auxiliary (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InversePreparation.assembly width (fresh, old))
      (InverseAssembly.auxiliaryPosition width index)).val = (fresh index).val := by
  change (InversePreparation.assembly width (fresh, old)
    (position width (InverseAssembly.auxiliaryPosition width index))).val = _
  rw [position_auxiliary]
  exact preparedLocalBasisEquiv_new_value (before width) auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) fresh old index

/-- Both original word segments retain their arbitrary incoming finite bits. -/
lemma selected_old (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin (width + width)) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InversePreparation.assembly width (fresh, old))
      (oldSourcePosition width index)).val =
        (old (oldPosition width index)).val := by
  change (InversePreparation.assembly width (fresh, old)
    (position width (oldSourcePosition width index))).val = _
  rw [position_old]
  exact preparedLocalBasisEquiv_old_value (before width) auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (auxiliary_fresh width)
    (auxiliary_disjoint width) fresh old (oldPosition width index)

private lemma old_value_combined_bit (width : Nat)
    (old : (before width).register.Index) (index : Fin (width + width)) :
    (old (oldPosition width index)).val =
      (finTwoEquiv.symm
        ((prodEquiv (m := width) (n := width) (inputBasisEquiv width old)).val.testBit
          index.rev.val)).val := by
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
  have combined : prodEquiv (m := width) (n := width) (inputBasisEquiv width old) =
      (inputQubitLayout width).binaryIndexEquiv raw := by
    change prodEquiv (m := width) (n := width)
      ((prodEquiv (m := width) (n := width)).symm
        ((inputQubitLayout width).binaryIndexEquiv raw)) = _
    exact (prodEquiv (m := width) (n := width)).apply_symm_apply _
  have bit :
      (prodEquiv (m := width) (n := width) (inputBasisEquiv width old)).val.testBit
        index.rev.val = finTwoEquiv (raw index) := by
    rw [combined]
    exact (inputQubitLayout width).binaryIndexEquiv_bit raw index
  rw [bit]
  exact stored.trans (congrArg (fun value : Fin 2 => value.val)
    (finTwoEquiv.symm_apply_apply (raw index))).symm

/-- The original input word is read at its canonical source addresses. -/
lemma selected_input (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin width) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InversePreparation.assembly width (fresh, old))
      (InverseAssembly.inputPosition width index)).val =
        (finTwoEquiv.symm ((inputBasisEquiv width old).1.val.testBit index.rev.val)).val := by
  let oldIndex : Fin (width + width) := ⟨index.val, by have bound := index.isLt; omega⟩
  have located : oldSourcePosition width oldIndex =
      InverseAssembly.inputPosition width index := by
    apply Fin.ext
    change (if index.val < width then InputPreparation.prefixWidth width + index.val
      else (encoding width).width + (index.val - width)) =
        (InverseAssembly.inputPosition width index).val
    rw [if_pos index.isLt]
    rfl
  rw [← located, selected_old]
  have bit := old_value_combined_bit width old oldIndex
  have reversed : oldIndex.rev.val = width + index.rev.val := by
    simp only [Fin.val_rev]
    change width + width - (index.val + 1) = width + (width - (index.val + 1))
    omega
  rw [reversed, prodEquiv_testBit_left] at bit
  exact bit

/-- The arbitrary XOR target is read at the rightmost original source word. -/
lemma selected_target (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) (index : Fin width) :
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width)
      (InversePreparation.assembly width (fresh, old))
      (InverseAssembly.targetPosition width index)).val =
        (finTwoEquiv.symm ((inputBasisEquiv width old).2.val.testBit index.rev.val)).val := by
  let oldIndex : Fin (width + width) := ⟨width + index.val, by
    have bound := index.isLt
    omega⟩
  have located : oldSourcePosition width oldIndex =
      InverseAssembly.targetPosition width index := by
    apply Fin.ext
    change (if width + index.val < width then InputPreparation.prefixWidth width +
      (width + index.val) else (encoding width).width + (width + index.val - width)) =
        (encoding width).width + index.val
    rw [if_neg (by omega)]
    omega
  rw [← located, selected_old]
  have bit := old_value_combined_bit width old oldIndex
  have reversed : oldIndex.rev.val = index.rev.val := by
    simp only [Fin.val_rev]
    change width + width - (width + index.val + 1) = width - (index.val + 1)
    omega
  rw [reversed, prodEquiv_testBit_right] at bit
  exact bit

/-- Decode the physically selected complete source and arbitrary target word. -/
def selectedWord (width : Nat) (basis : (after width).register.Index) :
    Fin (2 ^ (OutputCopy.encoding width).width) :=
  (QubitLayout.canonical (OutputCopy.encoding width).width).basisEquiv
    (UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width) basis)

private lemma selectedWord_bit (width : Nat) (basis : (after width).register.Index)
    (index : Fin (OutputCopy.encoding width).width) :
    (selectedWord width basis).val.testBit index.rev.val =
      finTwoEquiv (UnitaryCircuit.selectedInput (source width)
        (after width).quantumLayout (position width) (position_dimensions width)
        basis index) :=
  BinaryBasis.bigEndianEquiv_bit _ _ index

/-- Complete inverse source labels coincide with the explicit two-word assembly. -/
lemma selectedWord_assembly (width : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width).register.Index) :
    selectedWord width (InversePreparation.assembly width (fresh, old)) =
      InverseAssembly.basisEquiv width
        (InversePreparation.assembly width (fresh, old)) := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  let wire : Fin (OutputCopy.encoding width).width := bit.rev
  have undo : wire.rev = bit := Fin.rev_rev _
  rw [← undo]
  by_cases beforeInput : wire.val < InputPreparation.prefixWidth width
  · let auxiliary : Fin (InputPreparation.auxiliaryWidth width) := ⟨wire.val, by
      unfold InputPreparation.auxiliaryWidth
      omega⟩
    have located : InverseAssembly.auxiliaryPosition width auxiliary = wire := by
      apply Fin.ext
      change (if wire.val < InputPreparation.prefixWidth width then wire.val
        else width + wire.val) = wire.val
      rw [if_pos beforeInput]
    rw [← located, selectedWord_bit, InverseAssembly.basisEquiv_auxiliary]
    exact congrArg finTwoEquiv (Fin.ext (selected_auxiliary width fresh old auxiliary))
  · by_cases inInput : wire.val < InputPreparation.prefixWidth width + width
    · let input : Fin width := ⟨wire.val - InputPreparation.prefixWidth width, by omega⟩
      have located : InverseAssembly.inputPosition width input = wire := by
        apply Fin.ext
        change InputPreparation.prefixWidth width +
          (wire.val - InputPreparation.prefixWidth width) = wire.val
        omega
      rw [← located, selectedWord_bit, InverseAssembly.basisEquiv_input]
      have same :
          UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
            (position width) (position_dimensions width)
            (InversePreparation.assembly width (fresh, old))
            (InverseAssembly.inputPosition width input) =
              finTwoEquiv.symm ((inputBasisEquiv width old).1.val.testBit input.rev.val) := by
        apply Fin.ext
        exact selected_input width fresh old input
      rw [same, finTwoEquiv.apply_symm_apply]
    · by_cases beforeTarget : wire.val < (encoding width).width
      · let auxiliary : Fin (InputPreparation.auxiliaryWidth width) :=
          ⟨wire.val - width, by
            have complete := InputPreparation.complete_width width
            omega⟩
        have located : InverseAssembly.auxiliaryPosition width auxiliary = wire := by
          apply Fin.ext
          change (if wire.val - width < InputPreparation.prefixWidth width then
            wire.val - width else width + (wire.val - width)) = wire.val
          rw [if_neg (by omega)]
          omega
        rw [← located, selectedWord_bit, InverseAssembly.basisEquiv_auxiliary]
        exact congrArg finTwoEquiv
          (Fin.ext (selected_auxiliary width fresh old auxiliary))
      · let target : Fin width := ⟨wire.val - (encoding width).width, by
          have bound := wire.isLt
          change wire.val < (encoding width).width + width at bound
          omega⟩
        have located : InverseAssembly.targetPosition width target = wire := by
          apply Fin.ext
          change (encoding width).width + (wire.val - (encoding width).width) =
            wire.val
          omega
        rw [← located, selectedWord_bit, InverseAssembly.basisEquiv_target]
        have same :
            UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
              (position width) (position_dimensions width)
              (InversePreparation.assembly width (fresh, old))
              (InverseAssembly.targetPosition width target) =
                finTwoEquiv.symm ((inputBasisEquiv width old).2.val.testBit
                  target.rev.val) := by
          apply Fin.ext
          exact selected_target width fresh old target
        rw [same, finTwoEquiv.apply_symm_apply]

lemma selectedWord_eq_basisEquiv (width : Nat)
    (basis : (after width).register.Index) :
    selectedWord width basis = InverseAssembly.basisEquiv width basis := by
  let pair := (InversePreparation.assembly width).symm basis
  have assembled : InversePreparation.assembly width pair = basis :=
    (InversePreparation.assembly width).apply_symm_apply basis
  rw [← assembled]
  exact selectedWord_assembly width pair.1 pair.2

lemma selectedBasis_eq_basisEquiv (width : Nat)
    (basis : (after width).register.Index) :
    UnitaryCircuit.selectedInput (source width) (after width).quantumLayout
      (position width) (position_dimensions width) basis =
        (QubitLayout.canonical (OutputCopy.encoding width).width).basisEquiv.symm
          (InverseAssembly.basisEquiv width basis) := by
  apply (QubitLayout.canonical (OutputCopy.encoding width).width).basisEquiv.injective
  exact (selectedWord_eq_basisEquiv width basis).trans
    ((QubitLayout.canonical (OutputCopy.encoding width).width).basisEquiv.apply_symm_apply
      _).symm

/-- Place all actual native gates at the matching full-frame physical identities. -/
def program (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    UnitaryCircuit AlgorithmGate.model .empty (after width).quantumLayout :=
  UnitaryCircuit.placeAt (source width) (after width).quantumLayout
    (position width) (position_dimensions width) body

/-- The placed matrix reads source coordinates in their actual physical order. -/
lemma program_matrix_entry (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width))
    (row column : (after width).register.Index) :
    ((program width body).matrix environment) row column =
      (body.matrix environment)
        (UnitaryCircuit.basisAt (source width) (after width).quantumLayout
          (position width) (position_dimensions width) row)
        (UnitaryCircuit.basisAt (source width) (after width).quantumLayout
          (position width) (position_dimensions width) column) := by
  rw [program, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _
    (position_surjective width) _ row column

lemma program_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    (program width body).eventTrace = body.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

lemma program_eventCost (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    (program width body).eventCost = body.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- A proved native basis action remains exact after full-frame physical placement. -/
lemma program_apply_ket (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width))
    (input output : (source width).Basis)
    (actual : body.applyNormalized environment (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (targetInput targetOutput : (after width).register.Index)
    (inputSelected : UnitaryCircuit.selectedInput (source width)
      (after width).quantumLayout (position width) (position_dimensions width)
      targetInput = input)
    (outputSelected : UnitaryCircuit.selectedInput (source width)
      (after width).quantumLayout (position width) (position_dimensions width)
      targetOutput = output) :
    (program width body).applyNormalized environment (NormalizedVector.ket targetInput) =
      NormalizedVector.ket targetOutput := by
  apply UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    (source width) (after width).quantumLayout (position width)
    (position_dimensions width) body environment input output actual targetInput targetOutput
    inputSelected outputSelected
  funext index
  obtain ⟨sourceIndex, same⟩ := position_surjective width index.val
  have present : index.val ∈ Finset.univ.map (position width) := by
    rw [← same]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ sourceIndex)
  exact False.elim ((Finset.mem_compl.mp index.property) present)

/-- One live-context instruction executes the same complete native unitary. -/
def circuit (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width)) :
    Circuit (.quantum AlgorithmGate.model .empty) (after width) (after width) :=
  .unitary (program width body)

variable {Reference : Register} {H : Type} [Fintype H]

/-- Every hidden-state and reference block uses the same complete joint matrix. -/
lemma circuit_block_matrix (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width))
    (state : State (after width) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (store : Store (after width))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : H) :
    (((circuit width body).execute runtimeEnvironment Reference state).block
      (store, (hidden, (history, ())))).matrix =
      let operator := UnitaryOperator.prodTensor ((program width body).matrix
        runtimeEnvironment.quantum)
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator ((after width).register.prod Reference)) *
        (state.block (store, (hidden, history))).matrix *
          (operator : HilbertOperator ((after width).register.prod Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix runtimeEnvironment state (program width body) store hidden
    history

end

end QuantumAlg.MAU.Inversion.SharedEEA.InverseRuntimeFrame
