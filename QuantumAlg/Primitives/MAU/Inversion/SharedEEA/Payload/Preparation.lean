/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Input.PreparedFrame
import all QuantumAlg.Core.Execution.Owned.Qubits

/-!
# Actual supplied input, retained arithmetic payload, and one fixed preparation

The original n-bit input keeps its exact Work2 physical identities. Every
supplied payload bit follows the full shared-EEA frame and remains live and
charged. Modular-add inversion uses target plus flag; division uses numerator,
target, and flag. This is the same source fixed auxiliary preparation
[LYL+26, sec_EEA/sub_4phase.tex:104-117], with no input-dependent parameter.
Both widths may be zero. Preparation never erases or replaces supplied bits.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.PayloadPreparation

noncomputable section

open Execution

/-- Native frame followed by every supplied arithmetic payload bit. -/
def frameEncoding (width payloadWidth : Nat) :
    BinaryLabelEncoding (Registers width × Fin (2 ^ payloadWidth)) :=
  BinaryLabelEncoding.prod (SharedEEA.encoding width)
    (BinaryLabelEncoding.finIdentity payloadWidth)

/-- Supplied input positions keep their original Work2 identities; payload follows the full
  frame. -/
def physicalIndex (width index : Nat) : Nat :=
  if index < width then InputPreparation.prefixWidth width + index
  else (SharedEEA.encoding width).width + (index - width)

private theorem physicalIndex_injective (width payloadWidth : Nat) :
    Function.Injective (fun index : Fin (width + payloadWidth) => physicalIndex width
      index.val) := by
  intro left right same
  apply Fin.ext
  change physicalIndex width left.val = physicalIndex width right.val at same
  have leftBound := left.isLt
  have rightBound := right.isLt
  have complete := InputPreparation.complete_width width
  unfold InputPreparation.auxiliaryWidth InputPreparation.suffixWidth at complete
  unfold physicalIndex at same
  split at same <;> split at same <;> omega

/-- Exactly the original input and complete live payload, with no supplied EEA workspace. -/
def inputQubitLayout (width payloadWidth : Nat) : QubitLayout (width + payloadWidth) where
  physical_idx index := physicalIndex width index.val
  physical_idx_injective := physicalIndex_injective width payloadWidth

/-- Each supplied input and payload system is explicitly dimension two. -/
def inputLayout (width payloadWidth : Nat) : QuantumLayout (width + payloadWidth) :=
  (inputQubitLayout width payloadWidth).toQuantumLayout

/-- One supplied owned layout contains both the input and its arbitrary payload. -/
def before (width payloadWidth : Nat) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ (inputLayout width payloadWidth) (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem before_physical (width payloadWidth : Nat) :
    (before width payloadWidth).physicalIdx = (inputLayout width payloadWidth).identities := by
  change ((inputLayout width payloadWidth).wires ++ []).map QuantumWire.identity = _
  rw [List.append_nil, ← layout_identities_eq_map_wires]

private theorem input_wires (width payloadWidth : Nat) :
    (inputLayout width payloadWidth).wires = (before width payloadWidth).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change (inputLayout width payloadWidth).wires = (inputLayout width payloadWidth).wires ++ []
  exact (List.append_nil _).symm

/-- Read the actual supplied input and payload segments through their precise binary wire labels. -/
def inputBasisEquiv (width payloadWidth : Nat) :
    (before width payloadWidth).register.Index ≃ (Fin (2 ^ width) × Fin (2 ^ payloadWidth)) :=
  (basisOfEqualWires (inputLayout width payloadWidth) (before width payloadWidth).quantumLayout
    (input_wires width payloadWidth)).symm.trans
      ((inputQubitLayout width payloadWidth).binaryIndexEquiv.trans (prodEquiv (m := width) (n
        := payloadWidth)).symm)

/-- The existing source auxiliary allocation retains a distinct storage identity. -/
def auxiliaryKey : StorageKey := ⟨1⟩

theorem payloadPreparation_auxiliary_fresh (width payloadWidth : Nat) : auxiliaryKey ∉ (before
  width payloadWidth).keys := by
  change (⟨1⟩ : StorageKey) ∉ [⟨0⟩]
  decide

/-- Every new auxiliary wire is disjoint from both the actual input and actual payload. -/
theorem payloadPreparation_auxiliary_disjoint (width payloadWidth : Nat) :
    List.Disjoint (InputPreparation.auxiliaryLayout width).identities
      (before width payloadWidth).physicalIdx := by
  rw [before_physical]
  apply List.disjoint_left.mpr
  intro wire fresh old
  change wire ∈ List.ofFn (InputPreparation.auxiliaryPhysicalIndex width) at fresh
  change wire ∈ List.ofFn
    (fun index : Fin (width + payloadWidth) => physicalIndex width index.val) at old
  obtain ⟨newIndex, newPosition⟩ := List.mem_ofFn.mp fresh
  obtain ⟨oldIndex, oldPosition⟩ := List.mem_ofFn.mp old
  have newBound := newIndex.isLt
  have oldBound := oldIndex.isLt
  have complete := InputPreparation.complete_width width
  have freshBound := (InputAssembly.auxiliaryPosition width newIndex).isLt
  change InputPreparation.auxiliaryPhysicalIndex width newIndex <
    (SharedEEA.encoding width).width at freshBound
  unfold physicalIndex at oldPosition
  split at oldPosition
  · unfold InputPreparation.auxiliaryPhysicalIndex at newPosition
    split at newPosition <;> omega
  · omega

/-- The actual post-context owns all new auxiliary systems and the unchanged input and payload. -/
def after (width payloadWidth : Nat) : RuntimeCtx .quantum :=
  (before width payloadWidth).addOwnedLayout auxiliaryKey (InputPreparation.auxiliaryLayout width)
    (payloadPreparation_auxiliary_fresh width payloadWidth)
      (payloadPreparation_auxiliary_disjoint width payloadWidth)

/-- The preparation is the existing fixed source basis and depends only on the modulus. -/
def circuit (modulus payloadWidth : Nat) : Circuit (before modulus.size payloadWidth) (after
  modulus.size payloadWidth) :=
  .prepare (before modulus.size payloadWidth) auxiliaryKey (InputPreparation.auxiliaryLayout
    modulus.size)
    (payloadPreparation_auxiliary_fresh modulus.size payloadWidth)
      (payloadPreparation_auxiliary_disjoint modulus.size payloadWidth)
    (InputPreparation.preparation modulus)

/-- Exact actual fresh/old wire assembly, preserving all original quantum input and payload bits. -/
def assembly (width payloadWidth : Nat) :
    ((InputPreparation.auxiliaryLayout width).register.Index × (before width
      payloadWidth).register.Index) ≃
      (after width payloadWidth).register.Index :=
  preparedLocalBasisEquiv (before width payloadWidth) auxiliaryKey
    (InputPreparation.auxiliaryLayout width)
    (payloadPreparation_auxiliary_fresh width payloadWidth)
      (payloadPreparation_auxiliary_disjoint width payloadWidth)

/-- No additional hidden system accompanies the supplied payload or the existing auxiliary
  layout. -/
theorem payloadPreparation_total_width (width payloadWidth : Nat) :
    InputPreparation.auxiliaryWidth width + (width + payloadWidth) =
      (frameEncoding width payloadWidth).width := by
  change InputPreparation.auxiliaryWidth width + (width + payloadWidth) =
    (SharedEEA.encoding width).width + payloadWidth
  have complete := InputPreparation.complete_width width
  omega

/-- The one allocation event is the same fixed preparation on the real auxiliary wires. -/
theorem payloadPreparation_circuit_eventTrace (modulus payloadWidth : Nat) (path : (circuit
  modulus payloadWidth).Path) :
    (circuit modulus payloadWidth).eventTrace path = [(InputPreparation.preparation
      modulus).event] := rfl

private theorem auxiliary_space (width : Nat) :
    SpacePool.ofQuantumLayout (InputPreparation.auxiliaryLayout width) =
      OwnedQubits.space (InputPreparation.auxiliaryWidth width) := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (InputPreparation.auxiliaryQubitLayout width).toQuantumLayout_dimensionCount dimension

/-- Every supplied payload bit, including an arithmetic flag, is a counted owned system. -/
theorem payloadPreparation_before_resident (width payloadWidth : Nat) :
    (before width payloadWidth).residentSpace = OwnedQubits.space (width + payloadWidth) := by
  simp only [before, RuntimeCtx.residentSpace_addOwnedLayout, RuntimeCtx.residentSpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (inputQubitLayout width payloadWidth).toQuantumLayout_dimensionCount dimension

/-- The original input and entire supplied payload have the owned role. -/
theorem payloadPreparation_before_auxiliary (width payloadWidth : Nat) :
    (before width payloadWidth).auxiliarySpace = OwnedQubits.space (width + payloadWidth) := by
  simp only [before, RuntimeCtx.auxiliarySpace_addOwnedLayout, RuntimeCtx.auxiliarySpace_empty]
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (inputQubitLayout width payloadWidth).toQuantumLayout_dimensionCount dimension

private theorem combined_space (width payloadWidth : Nat) :
    OwnedQubits.space (InputPreparation.auxiliaryWidth width) +
      OwnedQubits.space (width + payloadWidth) =
        OwnedQubits.space (frameEncoding width payloadWidth).width := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      change (if (2 : ℕ+) = dimension then _ else 0) +
        (if (2 : ℕ+) = dimension then _ else 0) =
          if (2 : ℕ+) = dimension then _ else 0
      split_ifs
      · exact payloadPreparation_total_width width payloadWidth
      · rfl

/-- The complete actual resident pool contains the full frame and every supplied payload bit. -/
theorem payloadPreparation_after_resident (width payloadWidth : Nat) :
    (after width payloadWidth).residentSpace =
      OwnedQubits.space (frameEncoding width payloadWidth).width := by
  rw [after, RuntimeCtx.residentSpace_addOwnedLayout, auxiliary_space,
    payloadPreparation_before_resident]
  exact combined_space width payloadWidth

/-- Exactly the same real owned systems appear in the auxiliary pool. -/
theorem payloadPreparation_after_auxiliary (width payloadWidth : Nat) :
    (after width payloadWidth).auxiliarySpace =
      OwnedQubits.space (frameEncoding width payloadWidth).width := by
  rw [after, RuntimeCtx.auxiliarySpace_addOwnedLayout, auxiliary_space,
    payloadPreparation_before_auxiliary]
  exact combined_space width payloadWidth

end

end QuantumAlg.MAU.Inversion.SharedEEA.PayloadPreparation
