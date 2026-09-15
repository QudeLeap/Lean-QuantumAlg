/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Execution.Runtime
import all QuantumAlg.Core.Execution.Owned.Qubits
import all QuantumAlg.Core.Execution.Trace

/-!
# Independent resources of the actual prepared modular-add division

The independent envelope charges one fixed auxiliary preparation, both
complete corrected EEA passes, and actual variable Gidney multiplication.
All original denominator, numerator, target, and flag systems remain live
beside the original EEA auxiliaries [LYL+26, sec_EEA/sub_regshare.tex:16-26].
For n=size(N), resident and owned auxiliary space each contain exactly
4*n+4*size(n)+12 qubits and zero classical bits. Modulus one keeps the same
preparation and complete physical frame. These are conservative project
composition bounds, not the paper's measured-division space or leading gate count.
-/

namespace QuantumAlg.MAU.Division.SharedEEA.ExecutionResources

noncomputable section

open Execution ExecutionLayout Inversion.SharedEEA

/-- Three original words, their supplied flag, and the complete retained EEA auxiliary layout. -/
def width (inputWidth : Nat) : Nat := 4 * inputWidth + 4 * inputWidth.size + 12

/-- Independent dimension-aware capacity includes every supplied flag and all prepared systems. -/
def space (inputWidth : Nat) : SpacePool .quantum := OwnedQubits.space (width inputWidth)

/-- One actual fixed preparation coordinate and the independent complete native division
  envelope. -/
def events (modulus : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (InputPreparation.preparation modulus).event + nativeBudget modulus.size

/-- Fixed preparation plus both EEA passes and all actual variable-product stages. -/
def depthBound (inputWidth : Nat) : Nat := 1 + eventBound inputWidth

private theorem nativeSpace_eq (inputWidth : Nat) :
    OwnedQubits.space
        (PayloadPreparation.frameEncoding inputWidth (payloadWidth inputWidth)).width =
      space inputWidth := by
  apply congrArg OwnedQubits.space
  change (Inversion.SharedEEA.encoding inputWidth).width + payloadWidth inputWidth = width
    inputWidth
  rw [Inversion.SharedEEA.encoding_width]
  unfold payloadWidth width
  omega

/-- The actual resident pool contains exactly the independent complete physical layout. -/
theorem divisionResources_after_resident (inputWidth : Nat) :
    (after inputWidth).residentSpace = space inputWidth :=
  (PayloadPreparation.payloadPreparation_after_resident inputWidth (payloadWidth inputWidth)).trans
    (nativeSpace_eq inputWidth)

/-- The same supplied and prepared owned systems appear in the actual auxiliary pool. -/
theorem divisionResources_after_auxiliary (inputWidth : Nat) :
    (after inputWidth).auxiliarySpace = space inputWidth :=
  (PayloadPreparation.payloadPreparation_after_auxiliary inputWidth (payloadWidth inputWidth)).trans
    (nativeSpace_eq inputWidth)

private theorem nontrivial_cost (modulus : Nat) (nontrivial : 1 < modulus) :
    (ExecutionRuntime.nontrivialProgram modulus nontrivial).eventCost =
      (QuantumAlg.MAU.Division.SharedEEA.program modulus nontrivial).eventCost := by
  exact (UnitaryCircuit.reindex_eventCost (nativeLabelEquiv modulus.size)
    (ExecutionRuntime.flagProgram modulus nontrivial)).trans
      (UnitaryCircuit.prodLeft_eventCost (n := BinaryLabelEncoding.bool.width)
        (QuantumAlg.MAU.Division.SharedEEA.program modulus nontrivial))

private theorem native_pool (modulus : Nat) :
    (ExecutionRuntime.nativeProgram modulus).eventCost ≤ nativeBudget modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simp only [ExecutionRuntime.nativeProgram, dif_pos nontrivial, nontrivial_cost]
    exact divisionProgram_native_budget modulus nontrivial
  · simp only [ExecutionRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost]
    exact zero_le

/-- Exact actual preparation and native multiplicities meet the independent coordinatewise pool. -/
theorem divisionResources_resourcePool (modulus : Nat)
    (path : (ExecutionRuntime.code modulus).Path) :
    (ExecutionRuntime.code modulus).resourcePool path ≤ events modulus := by
  have actual := PayloadRuntime.payloadRuntime_code_resourcePool modulus (payloadWidth modulus.size)
    (ExecutionRuntime.nativeProgram modulus) (ExecutionRuntime.divisionExecution_native_within
      modulus)
    path
  exact actual.le.trans (add_le_add le_rfl (native_pool modulus))

/-- The actual execution peak includes every supplied and prepared system throughout both stages. -/
theorem divisionResources_resident (modulus : Nat)
    (path : (ExecutionRuntime.code modulus).Path) :
    (ExecutionRuntime.code modulus).peakResidentSpace path ≤ space modulus.size :=
  (PayloadRuntime.payloadRuntime_code_resident modulus (payloadWidth modulus.size)
    (ExecutionRuntime.nativeProgram modulus) (ExecutionRuntime.divisionExecution_native_within
      modulus)
    path).trans_eq (nativeSpace_eq modulus.size)

/-- Owned auxiliary peak comes from those same visited contexts, including the original flag. -/
theorem divisionResources_auxiliary (modulus : Nat)
    (path : (ExecutionRuntime.code modulus).Path) :
    (ExecutionRuntime.code modulus).peakAuxiliarySpace path ≤ space modulus.size :=
  (PayloadRuntime.payloadRuntime_code_auxiliary modulus (payloadWidth modulus.size)
    (ExecutionRuntime.nativeProgram modulus) (ExecutionRuntime.divisionExecution_native_within
      modulus)
    path).trans_eq (nativeSpace_eq modulus.size)

private theorem native_count (modulus : Nat) :
    (ExecutionRuntime.nativeProgram modulus).eventCost.card ≤ eventBound modulus.size := by
  by_cases nontrivial : 1 < modulus
  · simp only [ExecutionRuntime.nativeProgram, dif_pos nontrivial, nontrivial_cost]
    exact divisionProgram_event_count modulus nontrivial
  · simp only [ExecutionRuntime.nativeProgram, dif_neg nontrivial,
      UnitaryCircuit.identity_eventCost, Multiset.card_zero]
    exact Nat.zero_le _

/-- Unit-event depth counts preparation once and bounds the same complete native arithmetic. -/
theorem divisionResources_depth (modulus : Nat)
    (path : (ExecutionRuntime.code modulus).Path) :
    (ExecutionRuntime.code modulus).depth (fun _ => 1) path ≤ depthBound modulus.size := by
  have actual := PayloadRuntime.payloadRuntime_code_depth modulus (payloadWidth modulus.size)
    (ExecutionRuntime.nativeProgram modulus) (ExecutionRuntime.divisionExecution_native_within
      modulus)
    (fun _ => 1) path
  exact actual.le.trans (Nat.add_le_add_left
    ((ShiftResources.unitDepth_le_count _).trans (native_count modulus)) 1)

end

end QuantumAlg.MAU.Division.SharedEEA.ExecutionResources
