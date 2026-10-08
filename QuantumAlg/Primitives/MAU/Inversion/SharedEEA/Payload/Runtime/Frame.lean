/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Payload.Assembly
import all QuantumAlg.Core.Base.Layout.Quantum.IdentityPosition
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Actual runtime placement with an arbitrary retained payload

The runtime context stores auxiliary wires followed by the supplied input
and payload. The native gate addresses retain their original physical values,
which are all proved to occur in that exact context list. The adapter uses
the unique matching physical identity in the complete live layout; it does
not relabel physical wires or introduce a footprint-completing instruction.

Any actual native program on the same full frame can use this placement,
including the forward and reused inverse in measured division
[LYL+26, sec_point_add/sec_point_add.tex:51-79]. Its native trace and pool are
unchanged. The `Circuit.unitary` constructor remains the single execution
instruction, acting jointly with an arbitrary external reference.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntimeFrame

noncomputable section

open Execution PayloadPreparation

/-- Runtime order is fresh auxiliary wires followed by unchanged input and payload. -/
theorem after_physical (width payloadWidth : Nat) :
    (after width payloadWidth).physicalIdx =
      (InputPreparation.auxiliaryLayout width).identities ++ (inputLayout width
        payloadWidth).identities := by
  change ((InputPreparation.auxiliaryLayout width).wires ++ (before width
    payloadWidth).quantumWires).map
    QuantumWire.identity = _
  rw [List.map_append, ← layout_identities_eq_map_wires]
  change (InputPreparation.auxiliaryLayout width).identities ++ (before width
    payloadWidth).physicalIdx = _
  rw [PayloadPreparation.before_physical]

private theorem input_subset (width payloadWidth : Nat) :
    (InputPreparation.inputLayout width).identities ⊆ (inputLayout width
      payloadWidth).identities := by
  intro wire present
  change wire ∈ List.ofFn (fun index : Fin width =>
    InputPreparation.prefixWidth width + index.val) at present
  obtain ⟨index, position⟩ := List.mem_ofFn.mp present
  change wire ∈ List.ofFn (fun index : Fin (width + payloadWidth) => physicalIndex width index.val)
  refine List.mem_ofFn.mpr ⟨⟨index.val, by have bound := index.isLt; omega⟩, ?_⟩
  change (if index.val < width then InputPreparation.prefixWidth width + index.val
    else (encoding width).width + (index.val - width)) = wire
  rw [if_pos index.isLt]
  exact position

private theorem original_subset (width payloadWidth : Nat) :
    (InputPreparation.after width).physicalIdx ⊆ (after width payloadWidth).physicalIdx := by
  intro wire present
  rw [InputPreparation.after_physical] at present
  rw [after_physical]
  rcases List.mem_append.mp present with auxiliary | input
  · exact List.mem_append.mpr (Or.inl auxiliary)
  · exact List.mem_append.mpr (Or.inr (input_subset width payloadWidth input))

/-- Every native address belongs to the real context, including the supplied rightmost word. -/
theorem range_contained (width payloadWidth : Nat) :
    List.range (frameEncoding width payloadWidth).width ⊆ (after width
      payloadWidth).physicalIdx := by
  intro wire present
  have bound := List.mem_range.mp present
  change wire < (encoding width).width + payloadWidth at bound
  by_cases original : wire < (encoding width).width
  · exact original_subset width payloadWidth (InputPreparation.range_contained width
      (List.mem_range.mpr original))
  · rw [after_physical]
    apply List.mem_append.mpr
    right
    change wire ∈ List.ofFn (fun index : Fin (width + payloadWidth) => physicalIndex width
      index.val)
    let index : Fin (width + payloadWidth) :=
      ⟨width + (wire - (encoding width).width), by omega⟩
    refine List.mem_ofFn.mpr ⟨index, ?_⟩
    change (if width + (wire - (encoding width).width) < width then _
      else (encoding width).width + (width + (wire - (encoding width).width) - width)) = wire
    rw [if_neg (by omega)]
    omega

/-- The source native word retains its original physical addresses. -/
def source (width payloadWidth : Nat) : QuantumLayout (frameEncoding width payloadWidth).width :=
  (QubitLayout.canonical (frameEncoding width payloadWidth).width).toQuantum

private theorem source_contained (width payloadWidth : Nat) :
    (source width payloadWidth).identities ⊆ (after width
      payloadWidth).quantumLayout.identities := by
  rw [RuntimeCtx.runtimeCtx_quantumLayout_identities]
  change (QubitLayout.canonical (frameEncoding width payloadWidth).width).systemIdx ⊆
    (after width payloadWidth).physicalIdx
  rw [QubitLayout.canonical_systemIdx]
  exact range_contained width payloadWidth

/-- Each native address selects the live wire bearing that same physical identity. -/
def position (width payloadWidth : Nat) :
    Fin (frameEncoding width payloadWidth).width ↪ Fin (after width payloadWidth).systemCount :=
  QuantumLayout.positionOfIdentity (source width payloadWidth) (after width
    payloadWidth).quantumLayout
    (source_contained width payloadWidth)

theorem position_identity (width payloadWidth : Nat) (index : Fin (frameEncoding width
  payloadWidth).width) :
    ((after width payloadWidth).quantumLayout.wire (position width payloadWidth
      index)).identity = index.val :=
  QuantumLayout.positionOfIdentity_identity (source width payloadWidth)
    (after width payloadWidth).quantumLayout (source_contained width payloadWidth) index

private theorem before_count (width payloadWidth : Nat) : (before width
  payloadWidth).systemCount = width + payloadWidth := by
  change ((inputLayout width payloadWidth).wires ++ []).length = width + payloadWidth
  simp

private theorem after_count (width payloadWidth : Nat) :
    (after width payloadWidth).systemCount = InputPreparation.auxiliaryWidth width + (width +
      payloadWidth) := by
  change ((InputPreparation.auxiliaryLayout width).wires ++
    (before width payloadWidth).quantumWires).length = _
  rw [List.length_append, QuantumLayout.wires_length]
  exact congrArg (InputPreparation.auxiliaryWidth width + ·) (before_count width payloadWidth)

/-- The selected native positions cover the complete live frame and payload. -/
theorem position_surjective (width payloadWidth : Nat) : Function.Surjective (position width
  payloadWidth) := by
  have sameCount : (frameEncoding width payloadWidth).width = (after width
    payloadWidth).systemCount := by
    rw [after_count]
    have total := PayloadPreparation.payloadPreparation_total_width width payloadWidth
    omega
  let endomap := fun index : Fin (frameEncoding width payloadWidth).width =>
    Fin.cast sameCount.symm (position width payloadWidth index)
  have injective : Function.Injective endomap := by
    intro left right same
    apply (position width payloadWidth).injective
    exact Fin.cast_injective sameCount.symm same
  intro target
  obtain ⟨selected, same⟩ :=
    Finite.surjective_of_injective injective (Fin.cast sameCount.symm target)
  exact ⟨selected, Fin.cast_injective sameCount.symm same⟩

private theorem after_dimension (width payloadWidth : Nat) (index : Fin (after width
  payloadWidth).systemCount) :
    ((after width payloadWidth).quantumLayout.wire index).dimension = 2 := by
  have member : ((after width payloadWidth).quantumLayout.wire index) ∈
      (after width payloadWidth).quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  change ((after width payloadWidth).quantumLayout.wire index) ∈
    (InputPreparation.auxiliaryLayout width).wires ++ (before width payloadWidth).quantumWires
      at member
  rcases List.mem_append.mp member with fresh | old
  · change ((after width payloadWidth).quantumLayout.wire index) ∈
      (InputPreparation.auxiliaryQubitLayout width).toQuantumLayout.wires at fresh
    obtain ⟨located, same⟩ := List.mem_ofFn.mp fresh
    rw [← same]
    rfl
  · change ((after width payloadWidth).quantumLayout.wire index) ∈
      (inputLayout width payloadWidth).wires ++ [] at old
    have input := (List.mem_append.mp old).resolve_right (by simp)
    change ((after width payloadWidth).quantumLayout.wire index) ∈
      (inputQubitLayout width payloadWidth).toQuantumLayout.wires at input
    obtain ⟨located, same⟩ := List.mem_ofFn.mp input
    rw [← same]
    rfl

theorem position_dimensions (width payloadWidth : Nat) (index : Fin (frameEncoding width
  payloadWidth).width) :
    ((source width payloadWidth).wire index).dimension =
      ((after width payloadWidth).quantumLayout.wire (position width payloadWidth
        index)).dimension := by
  rw [after_dimension]
  rfl

private theorem before_wires (width payloadWidth : Nat) :
    (inputLayout width payloadWidth).wires = (before width payloadWidth).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width payloadWidth).wires = (inputLayout width payloadWidth).wires ++ []
  exact (List.append_nil _).symm

private def oldPosition (width payloadWidth : Nat) :
    Fin (width + payloadWidth) ≃ Fin (before width payloadWidth).systemCount :=
  positionsOfEqualWires (inputLayout width payloadWidth) (before width payloadWidth).quantumLayout
    (before_wires width payloadWidth)

private theorem oldPosition_identity (width payloadWidth : Nat) (index : Fin (width +
  payloadWidth)) :
    ((before width payloadWidth).quantumLayout.wire (oldPosition width payloadWidth
      index)).identity =
      physicalIndex width index.val := by
  have same := wireAtCorrespondingPosition (inputLayout width payloadWidth)
    (before width payloadWidth).quantumLayout (before_wires width payloadWidth) index
  exact congrArg QuantumWire.identity same

private def oldSourcePosition (width payloadWidth : Nat) (index : Fin (width + payloadWidth)) :
    Fin (frameEncoding width payloadWidth).width :=
  ⟨physicalIndex width index.val, by
    have bounded := index.isLt
    have complete := InputPreparation.complete_width width
    unfold InputPreparation.auxiliaryWidth at complete
    change physicalIndex width index.val < (encoding width).width + payloadWidth
    unfold physicalIndex
    split <;> omega⟩

/-- Fresh auxiliary positions select precisely the allocated physical bank. -/
theorem position_auxiliary (width payloadWidth : Nat)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    position width payloadWidth (PayloadAssembly.auxiliaryPosition width payloadWidth index) =
      PreparationBorrowed.fullPositionEquiv (before width payloadWidth) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width
          payloadWidth)
        (payloadPreparation_auxiliary_disjoint width payloadWidth) (.inl index) := by
  apply (after width payloadWidth).quantumLayout.identityInjective
  change ((after width payloadWidth).quantumLayout.wire
      (position width payloadWidth (PayloadAssembly.auxiliaryPosition width payloadWidth
        index))).identity =
    ((after width payloadWidth).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width payloadWidth) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width
          payloadWidth)
        (payloadPreparation_auxiliary_disjoint width payloadWidth) (.inl index))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_new_wire (before width payloadWidth)
    auxiliaryKey (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh
      width payloadWidth)
    (payloadPreparation_auxiliary_disjoint width payloadWidth) index
  exact (congrArg QuantumWire.identity same).symm

/-- Both originally supplied words retain their original physical identities. -/
theorem position_old (width payloadWidth : Nat) (index : Fin (width + payloadWidth)) :
    position width payloadWidth (oldSourcePosition width payloadWidth index) =
      PreparationBorrowed.fullPositionEquiv (before width payloadWidth) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width
          payloadWidth)
        (payloadPreparation_auxiliary_disjoint width payloadWidth) (.inr (oldPosition width
          payloadWidth index)) := by
  apply (after width payloadWidth).quantumLayout.identityInjective
  change ((after width payloadWidth).quantumLayout.wire
      (position width payloadWidth (oldSourcePosition width payloadWidth index))).identity =
    ((after width payloadWidth).quantumLayout.wire
      (PreparationBorrowed.fullPositionEquiv (before width payloadWidth) auxiliaryKey
        (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width
          payloadWidth)
        (payloadPreparation_auxiliary_disjoint width payloadWidth) (.inr (oldPosition width
          payloadWidth index)))).identity
  rw [position_identity]
  have same := PreparationBorrowed.fullPositionEquiv_old_wire (before width payloadWidth)
    auxiliaryKey (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh
      width payloadWidth)
    (payloadPreparation_auxiliary_disjoint width payloadWidth) (oldPosition width
      payloadWidth index)
  exact (oldPosition_identity width payloadWidth index).symm.trans
    (congrArg QuantumWire.identity same).symm

/-- Every fresh source bit reads its actual prepared auxiliary value. -/
theorem selected_auxiliary (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index)
    (index : Fin (InputPreparation.auxiliaryWidth width)) :
    (UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth)
      (PayloadPreparation.assembly width payloadWidth (fresh, old))
      (PayloadAssembly.auxiliaryPosition width payloadWidth index)).val = (fresh index).val := by
  change (PayloadPreparation.assembly width payloadWidth (fresh, old)
    (position width payloadWidth (PayloadAssembly.auxiliaryPosition width payloadWidth
      index))).val = _
  rw [position_auxiliary]
  exact preparedLocalBasisEquiv_new_value (before width payloadWidth) auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width payloadWidth)
    (payloadPreparation_auxiliary_disjoint width payloadWidth) fresh old index

/-- Both original word segments retain their arbitrary incoming finite bits. -/
theorem selected_old (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin (width + payloadWidth)) :
    (UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth)
      (PayloadPreparation.assembly width payloadWidth (fresh, old))
      (oldSourcePosition width payloadWidth index)).val =
        (old (oldPosition width payloadWidth index)).val := by
  change (PayloadPreparation.assembly width payloadWidth (fresh, old)
    (position width payloadWidth (oldSourcePosition width payloadWidth index))).val = _
  rw [position_old]
  exact preparedLocalBasisEquiv_old_value (before width payloadWidth) auxiliaryKey
    (InputPreparation.auxiliaryLayout width) (payloadPreparation_auxiliary_fresh width payloadWidth)
    (payloadPreparation_auxiliary_disjoint width payloadWidth) fresh old (oldPosition width
      payloadWidth index)

private theorem old_value_combined_bit (width payloadWidth : Nat)
    (old : (before width payloadWidth).register.Index) (index : Fin (width + payloadWidth)) :
    (old (oldPosition width payloadWidth index)).val =
      (finTwoEquiv.symm
        ((prodEquiv (m := width) (n := payloadWidth) (inputBasisEquiv width payloadWidth
          old)).val.testBit
          index.rev.val)).val := by
  let raw := (basisOfEqualWires (inputLayout width payloadWidth) (before width
    payloadWidth).quantumLayout
    (before_wires width payloadWidth)).symm old
  have stored := basisOfEqualWires_value (inputLayout width payloadWidth)
    (before width payloadWidth).quantumLayout (before_wires width payloadWidth) raw index
  change ((basisOfEqualWires (inputLayout width payloadWidth) (before width
    payloadWidth).quantumLayout
    (before_wires width payloadWidth))
      ((basisOfEqualWires (inputLayout width payloadWidth) (before width payloadWidth).quantumLayout
        (before_wires width payloadWidth)).symm old) (oldPosition width payloadWidth index)).val =
      (raw index).val at stored
  rw [Equiv.apply_symm_apply] at stored
  have combined : prodEquiv (m := width) (n := payloadWidth) (inputBasisEquiv width
    payloadWidth old) =
      (inputQubitLayout width payloadWidth).binaryIndexEquiv raw := by
    change prodEquiv (m := width) (n := payloadWidth)
      ((prodEquiv (m := width) (n := payloadWidth)).symm
        ((inputQubitLayout width payloadWidth).binaryIndexEquiv raw)) = _
    exact (prodEquiv (m := width) (n := payloadWidth)).apply_symm_apply _
  have bit :
      (prodEquiv (m := width) (n := payloadWidth) (inputBasisEquiv width payloadWidth
        old)).val.testBit
        index.rev.val = finTwoEquiv (raw index) := by
    rw [combined]
    exact (inputQubitLayout width payloadWidth).binaryIndexEquiv_bit raw index
  rw [bit]
  exact stored.trans (congrArg (fun value : Fin 2 => value.val)
    (finTwoEquiv.symm_apply_apply (raw index))).symm

/-- The original input word is read at its canonical source addresses. -/
theorem selected_input (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin width) :
    (UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth)
      (PayloadPreparation.assembly width payloadWidth (fresh, old))
      (PayloadAssembly.inputPosition width payloadWidth index)).val =
        (finTwoEquiv.symm ((inputBasisEquiv width payloadWidth old).1.val.testBit
          index.rev.val)).val := by
  let oldIndex : Fin (width + payloadWidth) := ⟨index.val, by have bound := index.isLt; omega⟩
  have located : oldSourcePosition width payloadWidth oldIndex =
      PayloadAssembly.inputPosition width payloadWidth index := by
    apply Fin.ext
    change (if index.val < width then InputPreparation.prefixWidth width + index.val
      else (encoding width).width + (index.val - width)) =
        (PayloadAssembly.inputPosition width payloadWidth index).val
    rw [if_pos index.isLt]
    rfl
  rw [← located, selected_old]
  have bit := old_value_combined_bit width payloadWidth old oldIndex
  have reversed : oldIndex.rev.val = payloadWidth + index.rev.val := by
    simp only [Fin.val_rev]
    change width + payloadWidth - (index.val + 1) = payloadWidth + (width - (index.val + 1))
    omega
  rw [reversed, prodEquiv_testBit_left] at bit
  exact bit

/-- The arbitrary XOR target is read at the rightmost original source word. -/
theorem selected_payload (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) (index : Fin payloadWidth) :
    (UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth)
      (PayloadPreparation.assembly width payloadWidth (fresh, old))
      (PayloadAssembly.payloadPosition width payloadWidth index)).val =
        (finTwoEquiv.symm ((inputBasisEquiv width payloadWidth old).2.val.testBit
          index.rev.val)).val := by
  let oldIndex : Fin (width + payloadWidth) := ⟨width + index.val, by
    have bound := index.isLt
    omega⟩
  have located : oldSourcePosition width payloadWidth oldIndex =
      PayloadAssembly.payloadPosition width payloadWidth index := by
    apply Fin.ext
    change (if width + index.val < width then InputPreparation.prefixWidth width +
      (width + index.val) else (encoding width).width + (width + index.val - width)) =
        (encoding width).width + index.val
    rw [if_neg (by omega)]
    omega
  rw [← located, selected_old]
  have bit := old_value_combined_bit width payloadWidth old oldIndex
  have reversed : oldIndex.rev.val = index.rev.val := by
    simp only [Fin.val_rev]
    change width + payloadWidth - (width + index.val + 1) = payloadWidth - (index.val + 1)
    omega
  rw [reversed, prodEquiv_testBit_right] at bit
  exact bit

/-- Decode the physically selected complete source and arbitrary target word. -/
def selectedWord (width payloadWidth : Nat) (basis : (after width payloadWidth).register.Index) :
    Fin (2 ^ (frameEncoding width payloadWidth).width) :=
  (QubitLayout.canonical (frameEncoding width payloadWidth).width).basisEquiv
    (UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth) basis)

private theorem selectedWord_bit (width payloadWidth : Nat) (basis : (after width
  payloadWidth).register.Index)
    (index : Fin (frameEncoding width payloadWidth).width) :
    (selectedWord width payloadWidth basis).val.testBit index.rev.val =
      finTwoEquiv (UnitaryCircuit.selectedInput (source width payloadWidth)
        (after width payloadWidth).quantumLayout (position width payloadWidth)
          (position_dimensions width payloadWidth)
        basis index) :=
  BinaryBasis.bigEndianEquiv_bit _ _ index

/-- Complete inverse source labels coincide with the explicit two-word assembly. -/
theorem selectedWord_assembly (width payloadWidth : Nat)
    (fresh : (InputPreparation.auxiliaryLayout width).register.Index)
    (old : (before width payloadWidth).register.Index) :
    selectedWord width payloadWidth (PayloadPreparation.assembly width payloadWidth (fresh, old)) =
      PayloadAssembly.basisEquiv width payloadWidth
        (PayloadPreparation.assembly width payloadWidth (fresh, old)) := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  let wire : Fin (frameEncoding width payloadWidth).width := bit.rev
  have undo : wire.rev = bit := Fin.rev_rev _
  rw [← undo]
  by_cases beforeInput : wire.val < InputPreparation.prefixWidth width
  · let auxiliary : Fin (InputPreparation.auxiliaryWidth width) := ⟨wire.val, by
      unfold InputPreparation.auxiliaryWidth
      omega⟩
    have located : PayloadAssembly.auxiliaryPosition width payloadWidth auxiliary = wire := by
      apply Fin.ext
      change (if wire.val < InputPreparation.prefixWidth width then wire.val
        else width + wire.val) = wire.val
      rw [if_pos beforeInput]
    rw [← located, selectedWord_bit, PayloadAssembly.payloadAssembly_basisEquiv_auxiliary]
    exact congrArg finTwoEquiv (Fin.ext (selected_auxiliary width payloadWidth fresh old auxiliary))
  · by_cases inInput : wire.val < InputPreparation.prefixWidth width + width
    · let input : Fin width := ⟨wire.val - InputPreparation.prefixWidth width, by omega⟩
      have located : PayloadAssembly.inputPosition width payloadWidth input = wire := by
        apply Fin.ext
        change InputPreparation.prefixWidth width +
          (wire.val - InputPreparation.prefixWidth width) = wire.val
        omega
      rw [← located, selectedWord_bit, PayloadAssembly.payloadAssembly_basisEquiv_input]
      have same :
          UnitaryCircuit.selectedInput (source width payloadWidth) (after width
            payloadWidth).quantumLayout
            (position width payloadWidth) (position_dimensions width payloadWidth)
            (PayloadPreparation.assembly width payloadWidth (fresh, old))
            (PayloadAssembly.inputPosition width payloadWidth input) =
              finTwoEquiv.symm ((inputBasisEquiv width payloadWidth old).1.val.testBit
                input.rev.val) := by
        apply Fin.ext
        exact selected_input width payloadWidth fresh old input
      rw [same, finTwoEquiv.apply_symm_apply]
    · by_cases beforeTarget : wire.val < (encoding width).width
      · let auxiliary : Fin (InputPreparation.auxiliaryWidth width) :=
          ⟨wire.val - width, by
            have complete := InputPreparation.complete_width width
            omega⟩
        have located : PayloadAssembly.auxiliaryPosition width payloadWidth auxiliary = wire := by
          apply Fin.ext
          change (if wire.val - width < InputPreparation.prefixWidth width then
            wire.val - width else width + (wire.val - width)) = wire.val
          rw [if_neg (by omega)]
          omega
        rw [← located, selectedWord_bit, PayloadAssembly.payloadAssembly_basisEquiv_auxiliary]
        exact congrArg finTwoEquiv
          (Fin.ext (selected_auxiliary width payloadWidth fresh old auxiliary))
      · let target : Fin payloadWidth := ⟨wire.val - (encoding width).width, by
          have bound := wire.isLt
          change wire.val < (encoding width).width + payloadWidth at bound
          omega⟩
        have located : PayloadAssembly.payloadPosition width payloadWidth target = wire := by
          apply Fin.ext
          change (encoding width).width + (wire.val - (encoding width).width) =
            wire.val
          omega
        rw [← located, selectedWord_bit, PayloadAssembly.payloadAssembly_basisEquiv_payload]
        have same :
            UnitaryCircuit.selectedInput (source width payloadWidth) (after width
              payloadWidth).quantumLayout
              (position width payloadWidth) (position_dimensions width payloadWidth)
              (PayloadPreparation.assembly width payloadWidth (fresh, old))
              (PayloadAssembly.payloadPosition width payloadWidth target) =
                finTwoEquiv.symm ((inputBasisEquiv width payloadWidth old).2.val.testBit
                  target.rev.val) := by
          apply Fin.ext
          exact selected_payload width payloadWidth fresh old target
        rw [same, finTwoEquiv.apply_symm_apply]

theorem selectedWord_eq_basisEquiv (width payloadWidth : Nat)
    (basis : (after width payloadWidth).register.Index) :
    selectedWord width payloadWidth basis = PayloadAssembly.basisEquiv width payloadWidth
      basis := by
  let pair := (PayloadPreparation.assembly width payloadWidth).symm basis
  have assembled : PayloadPreparation.assembly width payloadWidth pair = basis :=
    (PayloadPreparation.assembly width payloadWidth).apply_symm_apply basis
  rw [← assembled]
  exact selectedWord_assembly width payloadWidth pair.1 pair.2

theorem selectedBasis_eq_basisEquiv (width payloadWidth : Nat)
    (basis : (after width payloadWidth).register.Index) :
    UnitaryCircuit.selectedInput (source width payloadWidth) (after width
      payloadWidth).quantumLayout
      (position width payloadWidth) (position_dimensions width payloadWidth) basis =
        (QubitLayout.canonical (frameEncoding width payloadWidth).width).basisEquiv.symm
          (PayloadAssembly.basisEquiv width payloadWidth basis) := by
  apply (QubitLayout.canonical (frameEncoding width payloadWidth).width).basisEquiv.injective
  exact (selectedWord_eq_basisEquiv width payloadWidth basis).trans
    ((QubitLayout.canonical (frameEncoding width payloadWidth).width).basisEquiv.apply_symm_apply
      _).symm

/-- Place all actual native gates at the matching full-frame physical identities. -/
def program (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth)) :
    UnitaryCircuit AlgorithmGate.model .empty (after width payloadWidth).quantumLayout :=
  UnitaryCircuit.placeAt (source width payloadWidth) (after width payloadWidth).quantumLayout
    (position width payloadWidth) (position_dimensions width payloadWidth) body

/-- The placed matrix reads source coordinates in their actual physical order. -/
theorem program_matrix_entry (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth))
    (row column : (after width payloadWidth).register.Index) :
    (program width payloadWidth body).matrix row column =
      body.matrix
        (UnitaryCircuit.basisAt (source width payloadWidth) (after width payloadWidth).quantumLayout
          (position width payloadWidth) (position_dimensions width payloadWidth) row)
        (UnitaryCircuit.basisAt (source width payloadWidth) (after width payloadWidth).quantumLayout
          (position width payloadWidth) (position_dimensions width payloadWidth) column) := by
  rw [program, UnitaryCircuit.placeAt_matrix]
  exact UnitaryCircuit.operatorAt_entry_of_surjective _ _ _ _
    (position_surjective width payloadWidth) _ row column

theorem program_eventTrace (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth)) :
    (program width payloadWidth body).eventTrace = body.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

theorem program_eventCost (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth)) :
    (program width payloadWidth body).eventCost = body.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

/-- A proved native basis action remains exact after full-frame physical placement. -/
theorem program_apply_ket (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth))
    (input output : (source width payloadWidth).Basis)
    (actual : body.applyNormalized (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (targetInput targetOutput : (after width payloadWidth).register.Index)
    (inputSelected : UnitaryCircuit.selectedInput (source width payloadWidth)
      (after width payloadWidth).quantumLayout (position width payloadWidth)
        (position_dimensions width payloadWidth)
      targetInput = input)
    (outputSelected : UnitaryCircuit.selectedInput (source width payloadWidth)
      (after width payloadWidth).quantumLayout (position width payloadWidth)
        (position_dimensions width payloadWidth)
      targetOutput = output) :
    (program width payloadWidth body).applyNormalized (NormalizedVector.ket targetInput) =
      NormalizedVector.ket targetOutput := by
  apply UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    (source width payloadWidth) (after width payloadWidth).quantumLayout (position width
      payloadWidth)
    (position_dimensions width payloadWidth) body input output actual targetInput targetOutput
    inputSelected outputSelected
  funext index
  obtain ⟨sourceIndex, same⟩ := position_surjective width payloadWidth index.val
  have present : index.val ∈ Finset.univ.map (position width payloadWidth) := by
    rw [← same]
    exact Finset.mem_map_of_mem _ (Finset.mem_univ sourceIndex)
  exact False.elim ((Finset.mem_compl.mp index.property) present)

/-- One live-context instruction executes the same complete native unitary. -/
def circuit (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth)) :
    Circuit (.quantum AlgorithmGate.model .empty) (after width payloadWidth) (after width
      payloadWidth) :=
  .unitary (program width payloadWidth body)

variable {Reference : Register} {H : Type} [Fintype H]

/-- Every hidden-state and reference block uses the same complete joint matrix. -/
theorem circuit_block_matrix (width payloadWidth : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (source width payloadWidth))
    (state : State (after width payloadWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × H))
    (store : Store (after width payloadWidth))
    (hidden : ClassicalOracleModel.empty.HiddenState) (history : H) :
    (((circuit width payloadWidth body).execute Reference state).block
      (store, (hidden, (history, ())))).matrix =
      let operator := UnitaryOperator.prodTensor (program width payloadWidth body).matrix
        (1 : UnitaryOperator Reference)
      (operator : HilbertOperator ((after width payloadWidth).register.prod Reference)) *
        (state.block (store, (hidden, history))).matrix *
          (operator : HilbertOperator ((after width payloadWidth).register.prod
            Reference)).conjTranspose :=
  Circuit.execute_unitary_block_matrix state (program width payloadWidth body) store hidden history

end

end QuantumAlg.MAU.Inversion.SharedEEA.PayloadRuntimeFrame
