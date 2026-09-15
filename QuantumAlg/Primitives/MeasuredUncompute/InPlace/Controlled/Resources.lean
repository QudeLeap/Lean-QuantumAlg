/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Runtime
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Resources

/-!
# Resources of the actual controlled measured arithmetic body

Every original arithmetic event acquires its actual emitted quantum-control
coordinate. The inactive copy and phase correction are controlled and charged
too. The H/Z/reset and final three-CNOT swap remain unconditional. One real
owned control augments the original three-word frame, without another field
bank, and all n finite measurement cells remain live. The actual body allocates
nothing. Its extension of the source arithmetic is a project construction
[LYL+26, sec_point_add/sec_point_add.tex:24-36,52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA MAU.Multiplication

/-- Complete live storage includes the real coherent control and all retained measurement cells. -/
def space (width : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) + OwnedQubits.space (3 * width + 4 * width.size + 12)

private def copyBudget (width : Nat) : ResourcePool .quantum :=
  width • ResourcePool.singleton (.gate (.builtin "cnot"))

private def maskBudget (width : Nat) : ResourcePool .quantum :=
  width • ResourcePool.singleton (Gate.atomicEvent (.declared "QuantumAlg.Components.Gate"
    "pauli-z"))

private def saveBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 (VariableGidney.nativeBudget width) +
    ResourcePool.controlForDimension 2 (copyBudget width)

private def correctionBudget (width : Nat) : ResourcePool .quantum :=
  ResourcePool.controlForDimension 2 (NativeProductCorrection.nativeBudget width) +
    ResourcePool.controlForDimension 2 (maskBudget width)

/-- Independent event allowance before the one real unconditional measurement sequence. -/
def beforeBudget (operation : InPlaceTarget.Operation) (width : Nat) : ResourcePool .quantum :=
  match operation with
  | .division => ResourcePool.controlForDimension 2 (NativeBudget.inPlace width) + saveBudget width
  | .multiplication => saveBudget width

/-- Independent event allowance for the actual stored correction and full final swap. -/
def afterBudget (operation : InPlaceTarget.Operation) (width : Nat) : ResourcePool .quantum :=
  match operation with
  | .division => ResourcePool.controlForDimension 2 (NativeBudget.inPlace width) +
      (correctionBudget width + (3 * width) • ResourcePool.singleton (.gate (.builtin "cnot")))
  | .multiplication => ResourcePool.controlForDimension 2 (NativeBudget.inPlace width) +
      (correctionBudget width +
        (ResourcePool.controlForDimension 2 (NativeBudget.inPlace width) +
          (3 * width) • ResourcePool.singleton (.gate (.builtin "cnot"))))

/-- All allowances are independent width formulas, in the same three-block execution order. -/
def events (operation : InPlaceTarget.Operation) (width : Nat) : ResourcePool .quantum :=
  beforeBudget operation width + (NumeratorReset.budget width + afterBudget operation width)

/-- Serial dependence includes H, all Z writes, and the selected reset before the final
correction. -/
def depthBound (operation : InPlaceTarget.Operation) (width : Nat) : Nat :=
  (beforeBudget operation width).card + ((1 + 2 * width) + (afterBudget operation width).card)

private theorem copy_cost (width : Nat) : (copy width).eventCost = copyBudget width := by
  have actual : (EncodedBit.Word.xorIntoGates (FramePorts.numerator width)
      (FramePorts.accumulator width)
      (fun index => (FramePorts.accumulator_numerator_ne width index index).symm)).map
        EncodedBit.GateSpec.event = List.replicate width (.gate (.builtin "cnot")) := by
    rw [EncodedBit.Word.xorIntoGates, List.map_ofFn]
    change List.ofFn (fun _ : Fin width =>
      (Resource.Event.gate (.builtin "cnot") : Resource.Event .quantum)) = _
    exact List.ofFn_const _ _
  have trace : (copy width).eventTrace = List.replicate width (.gate (.builtin "cnot")) :=
    (EncodedBit.GateSpec.programList_eventTrace _).trans actual
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, trace, ResourcePool.ofList_replicate]
  rfl

private theorem mask_cost (width : Nat) (value : CShape.Value (.fixedVector width (.finite 2))) :
    (inactiveMask width value).eventCost ≤ maskBudget width := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, inactiveMask,
    EncodedBit.Word.PhaseCorrection.program,
    EncodedBit.Word.PhaseCorrection.phaseCorrection_sequence_trace, ResourcePool.ofList_replicate]
  apply ResourcePool.le_iff_count.mpr
  intro event
  rw [maskBudget, ResourcePool.count_scale, ResourcePool.count_nsmul]
  exact Nat.mul_le_mul_right _
    (EncodedBit.Word.PhaseCorrection.phaseCorrection_selected_count_le (QubitReadouts.mask value))

private theorem controlled_bound (width : Nat) (active : Fin 2)
    (program : UnitaryCircuit (Qubits (frameWidth width)))
    (within : program.physical_idx ⊆ List.range (frameWidth width))
    (budget : ResourcePool .quantum) (bounded : program.eventCost ≤ budget) :
    (controlled width active program within).eventCost ≤ ResourcePool.controlForDimension 2
      budget := by
  rw [controlled_cost]
  exact (ResourcePool.controlForDimension_le_controlForDimension_iff 2).mpr bounded

private theorem forward_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventCost ≤ ResourcePool.controlForDimension 2
      (NativeBudget.inPlace modulus.size) := by
  apply controlled_bound
  exact (InPlaceDivisionResources.forward_cost modulus prime).le.trans
    (NativeBudget.inPlace_bound modulus prime.one_lt)

private theorem backward_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (backward modulus prime).eventCost ≤ ResourcePool.controlForDimension 2
      (NativeBudget.inPlace modulus.size) := by
  apply controlled_bound
  exact (InPlaceDivisionResources.backward_cost modulus prime).le.trans
    (NativeBudget.inPlace_bound modulus prime.one_lt)

private theorem reused_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (reusedForward modulus prime).eventCost ≤ ResourcePool.controlForDimension 2
      (NativeBudget.inPlace modulus.size) := by
  apply controlled_bound
  exact ((NativeReusedEEA.forward_cost modulus prime).trans
    (InPlaceDivisionResources.backward_cost modulus prime)).le.trans
      (NativeBudget.inPlace_bound modulus prime.one_lt)

private theorem save_cost_bound (modulus : Nat) :
    (save modulus).eventCost ≤ saveBudget modulus.size := by
  rw [save, UnitaryCircuit.seq_eventCost]
  exact add_le_add
    (controlled_bound _ _ _ _ _ (NativeProductFrame.nativeProductFrame_budget _ _))
    (controlled_bound _ _ _ _ _ (copy_cost modulus.size).le)

private theorem correction_cost_bound (modulus : Nat)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (correction modulus value).eventCost ≤ correctionBudget modulus.size := by
  rw [correction, UnitaryCircuit.seq_eventCost]
  exact add_le_add
    (controlled_bound _ _ _ _ _ (ReusedProduct.correction_budget modulus.size
      (InPlaceArithmetic.modulusWord modulus) (QubitReadouts.mask value)))
    (controlled_bound _ _ _ _ _ (mask_cost modulus.size value))

private theorem swap_cost_bound (width : Nat) :
    (swap width).eventCost ≤ (3 * width) • ResourcePool.singleton (.gate (.builtin "cnot")) := by
  have actual : (swap width).eventCost = (FrameSwap.program width).eventCost := by
    have trace : (swap width).eventTrace = (FrameSwap.program width).eventTrace :=
      uncontrolled_trace width (FrameSwap.program width) _
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, trace,
      UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  have oldPool := InPlaceDivisionResources.native_pool width (FrameSwap.program width)
    (InPlaceDivision.full_within width _ (FrameSwap.frameSwap_physical width)) ()
  exact actual.le.trans (oldPool.symm.le.trans (InPlaceDivisionResources.swap_budget width ()))

/-- The native prefix's literal events meet the independently prescribed controlled coordinates. -/
theorem beforeReset_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    (beforeReset operation modulus prime).eventCost ≤ beforeBudget operation modulus.size := by
  cases operation
  · exact save_cost_bound modulus
  · exact add_le_add (forward_cost_bound modulus prime) (save_cost_bound modulus)

/-- Every actual stored vector selects a suffix within the same independent native allowance. -/
theorem suffix_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (suffix operation modulus prime value).eventCost ≤ afterBudget operation modulus.size := by
  cases operation
  · exact add_le_add (reused_cost_bound modulus prime)
      (add_le_add (correction_cost_bound modulus value)
        (add_le_add (backward_cost_bound modulus prime) (swap_cost_bound modulus.size)))
  · exact add_le_add (backward_cost_bound modulus prime)
      (add_le_add (correction_cost_bound modulus value) (swap_cost_bound modulus.size))

private theorem native_pool (width : Nat)
    (program : UnitaryCircuit (Qubits (1 + frameWidth width)))
    (within : program.physical_idx ⊆ List.range (1 + frameWidth width))
    (path : (nativeCode width program within).Path) :
    (nativeCode width program within).resourcePool path = program.eventCost := by
  change ResourcePool.ofList (runtimeProgram width program).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, runtimeProgram_cost]

private theorem reset_budget (width : Nat) (path : (reset width).Path) :
    (reset width).resourcePool path ≤ NumeratorReset.budget width := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv (NumeratorReset.code width)
    (reset_local width) (controlContext width) (control_disjoint width)).surjective path
  exact (ContextUnion.frameLocal_resourcePool (NumeratorReset.code width) (reset_local width)
    (controlContext width) (control_disjoint width) original).le.trans
      (NumeratorReset.code_budget width original)

/-- Each path of the actual emitted body pays its complete controlled and measured event pool. -/
theorem body_budget (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime).Path) :
    (body operation modulus prime).resourcePool path ≤ events operation modulus.size := by
  change ResourcePool.ofList
    ((nativeCode modulus.size (beforeReset operation modulus prime)
      (beforeReset_within operation modulus prime)).eventTrace path.1 ++
      ((reset modulus.size).eventTrace path.2.1 ++
        (selectedSuffix operation modulus prime).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add ((native_pool _ _ _ _).le.trans (beforeReset_budget operation modulus prime))
    (add_le_add (reset_budget modulus.size path.2.1)
      ((native_pool _ _ _ _).le.trans (suffix_budget operation modulus prime path.2.2.1)))

private theorem native_depth (width : Nat)
    (program : UnitaryCircuit (Qubits (1 + frameWidth width)))
    (within : program.physical_idx ⊆ List.range (1 + frameWidth width))
    (path : (nativeCode width program within).Path) :
    (nativeCode width program within).depth (fun _ => 1) path ≤ program.eventCost.card := by
  change program.evaluatedEventDepth (fun _ => 1) + 0 ≤ _
  rw [Nat.add_zero]
  exact ShiftResources.unitDepth_le_count program

private theorem reset_depth (width : Nat) (path : (reset width).Path) :
    (reset width).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  obtain ⟨original, rfl⟩ := (ContextUnion.frameLocalPathEquiv (NumeratorReset.code width)
    (reset_local width) (controlContext width) (control_disjoint width)).surjective path
  exact (ContextUnion.frameLocal_depth (NumeratorReset.code width) (reset_local width)
    (controlContext width) (control_disjoint width) (fun _ => 1) original).le.trans
      (NumeratorReset.code_depth width original)

/-- The actual serial execution meets its independent native and feed-forward depth allowance. -/
theorem body_depth (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body operation modulus prime).Path) :
    (body operation modulus prime).depth (fun _ => 1) path ≤ depthBound operation modulus.size := by
  change (nativeCode modulus.size (beforeReset operation modulus prime)
      (beforeReset_within operation modulus prime)).depth (fun _ => 1) path.1 +
    ((reset modulus.size).depth (fun _ => 1) path.2.1 +
      (nativeCode modulus.size (suffix operation modulus prime path.2.2.1)
        (suffix_within operation modulus prime path.2.2.1)).depth (fun _ => 1) path.2.2.2) ≤ _
  exact Nat.add_le_add
    ((native_depth _ _ _ _).trans (Multiset.card_le_card (beforeReset_budget operation modulus
      prime)))
    (Nat.add_le_add (reset_depth modulus.size path.2.1)
      ((native_depth _ _ _ _).trans
        (Multiset.card_le_card (suffix_budget operation modulus prime path.2.2.1))))

/-- Actual event multiplicities also give the complete event-count allowance. -/
theorem body_event_count (operation : InPlaceTarget.Operation) (modulus : Nat) (prime :
    Nat.Prime modulus)
    (path : (body operation modulus prime).Path) :
    ((body operation modulus prime).eventTrace path).length ≤ (events operation
      modulus.size).card :=
  Multiset.card_le_card (body_budget operation modulus prime path)

private theorem control_resident (width : Nat) :
    (controlContext width).residentSpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (controlQubitLayout width).toQuantumLayout_dimensionCount dimension

private theorem control_auxiliary (width : Nat) :
    (controlContext width).auxiliarySpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (controlQubitLayout width).toQuantumLayout_dimensionCount dimension

private theorem ownedSpace_add (left right : Nat) :
    OwnedQubits.space (left + right) = OwnedQubits.space left + OwnedQubits.space right := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      by_cases binary : (2 : ℕ+) = dimension <;> simp [OwnedQubits.space, binary]

private theorem one_control_space (width : Nat) :
    InPlaceDivisionResources.space width + OwnedQubits.space 1 = space width := by
  rw [InPlaceDivisionResources.space, add_assoc, ← ownedSpace_add]
  have count : 3 * width + 4 * width.size + 11 + 1 = 3 * width + 4 * width.size + 12 := by omega
  rw [count]
  rfl

/-- The complete actual context charges the additional owned control as exactly one qubit. -/
theorem context_resident (width : Nat) : (context width).residentSpace = space width := by
  rw [context, RuntimeCtx.residentSpace_disjointUnion,
    InPlaceDivisionResources.context_resident, control_resident]
  exact one_control_space width

theorem context_auxiliary (width : Nat) : (context width).auxiliarySpace = space width := by
  rw [context, RuntimeCtx.auxiliarySpace_disjointUnion,
    InPlaceDivisionResources.context_auxiliary, control_auxiliary]
  exact one_control_space width

/-- Every actual execution path keeps exactly the full three-word frame, control and finite cells.
-/
theorem body_resident (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime).Path) :
    (body operation modulus prime).peakResidentSpace path = space modulus.size := by
  have upper := (body operation modulus prime).peakResidentSpace_le_of_visited path
    (context modulus.size).residentSpace (by
      intro visited present
      rw [ContextUnion.local_visited _ (body_isLocal operation modulus prime) path visited present])
  have lower := (body operation modulus prime).residentSpace_le_peak_of_visited path
    (context modulus.size) (ContextUnion.local_pre_mem _ (body_isLocal operation modulus prime)
      path)
  exact (le_antisymm upper lower).trans (context_resident modulus.size)

theorem body_auxiliary (operation : InPlaceTarget.Operation) (modulus : Nat) (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime).Path) :
    (body operation modulus prime).peakAuxiliarySpace path = space modulus.size := by
  have upper := (body operation modulus prime).peakAuxiliarySpace_le_of_visited path
    (context modulus.size).auxiliarySpace (by
      intro visited present
      rw [ContextUnion.local_visited _ (body_isLocal operation modulus prime) path visited present])
  have lower := (body operation modulus prime).auxiliarySpace_le_peak_of_visited path
    (context modulus.size) (ContextUnion.local_pre_mem _ (body_isLocal operation modulus prime)
      path)
  exact (le_antisymm upper lower).trans (context_auxiliary modulus.size)

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
