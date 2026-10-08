/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Inverse.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Independent resources of the actual measured in-place division circuit

Two complete in-place EEA passes, the original product, H/Z/reset, the
selected recompute/Z/uncompute correction, and the real final swap are all
charged at their native coordinates [LYL+26, sec_point_add/sec_point_add.tex:45-105].
The EEA bound is the proved finite-selector implementation bound, not the
paper's leading constant and not the standalone XOR inverse's extra copy.

For n=size(p), the complete live capacity is 3*n+4*size(n)+11 qubits and
n retained finite-bit cells. The external Reference remains external.
Classical allocation emits no native event but contributes its actual
capacity; both selected branches read already retained results.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceDivisionResources

noncomputable section

open Execution MAU.Inversion.SharedEEA MAU.Multiplication InPlaceDivision

/-- The full original three-word frame plus the n real finite measurement cells. -/
def space (width : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) +
    OwnedQubits.space (3 * width + 4 * width.size + 11)

/-- Every independent native allowance appears in the actual six-block execution order. -/
def bodyBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  NativeBudget.inPlace width +
    (VariableGidney.nativeBudget width +
      (NumeratorReset.budget width +
        (NativeBudget.inPlace width +
          (NativeProductCorrection.nativeBudget width +
            (3 * width) • ResourcePool.singleton
              (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)))))

/-- Per-wire zero preparation, fixed-seed X loading and the bounded native body. -/
def events (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
    (EncodedBit.Word.BasisLoad.xCount (InPlacePreparation.loadConstant modulus) •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit)) +
    bodyBudget modulus.size

/-- Serial depth keeps all inter-block dependencies, including both stored-result corrections. -/
def bodyDepth (width : Nat) : Nat :=
  (NativeBudget.inPlace width).card +
    ((VariableGidney.nativeBudget width).card +
      ((1 + 2 * width) +
        ((NativeBudget.inPlace width).card +
          ((NativeProductCorrection.nativeBudget width).card + 3 * width))))

/-- Zero preparation and fixed X loading precede the measured native body. -/
def depthBound (width : Nat) : Nat :=
  1 + InputPreparation.auxiliaryWidth width + bodyDepth width

private theorem load_pool (modulus : Nat) :
    (InPlacePreparation.loadProgram modulus).eventCost =
      EncodedBit.Word.BasisLoad.xCount (InPlacePreparation.loadConstant modulus) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit) := by
  exact (Execution.PreparationLoaded.program_eventCost
    (InversePreparation.before modulus.size) InversePreparation.auxiliaryKey
    (InputPreparation.auxiliaryLayout modulus.size)
    (InversePreparation.auxiliary_fresh modulus.size)
    (InversePreparation.auxiliary_disjoint modulus.size) _).trans
      (EncodedBit.Word.BasisLoad.basisLoad_eventCost
        (InputPreparation.auxiliaryQubitLayout modulus.size) .empty
        (InPlacePreparation.loadConstant modulus))

private theorem load_depth (modulus : Nat) :
    (InPlacePreparation.loadProgram modulus).evaluatedEventDepth (fun _ => 1) ≤
      InputPreparation.auxiliaryWidth modulus.size := by
  have placed : (InPlacePreparation.loadProgram modulus).evaluatedEventDepth (fun _ => 1) =
      (EncodedBit.Word.BasisLoad.program (InputPreparation.auxiliaryQubitLayout modulus.size)
        .empty (InPlacePreparation.loadConstant modulus)).evaluatedEventDepth (fun _ => 1) :=
    Execution.PreparationLoaded.program_unitDepth
      (InversePreparation.before modulus.size) InversePreparation.auxiliaryKey
      (InputPreparation.auxiliaryLayout modulus.size)
      (InversePreparation.auxiliary_fresh modulus.size)
      (InversePreparation.auxiliary_disjoint modulus.size) _
  rw [placed, EncodedBit.Word.BasisLoad.basisLoad_unitDepth]
  exact EncodedBit.Word.BasisLoad.basisLoad_count_le _

private theorem native_pool (width : Nat)
    (member : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (path : (NumeratorRuntime.code width member).Path) :
    (NumeratorRuntime.code width member).resourcePool path = member.eventCost := by
  change ResourcePool.ofList (NumeratorRuntime.program width member).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, NumeratorRuntime.program_cost]

private theorem forward_cost (modulus : Nat) (prime : Nat.Prime modulus) :
    (NativeEEAFrame.forward modulus prime).eventCost =
      (InPlaceForward.program modulus prime.one_lt).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    NativeEEAFrame.nativeEEAFrame_forward_trace,
    InPlaceForward.inPlaceForward_nativeProgram_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

private theorem backward_cost (modulus : Nat) (prime : Nat.Prime modulus) :
    (NativeEEAFrame.backward modulus prime).eventCost =
      (InPlaceForward.program modulus prime.one_lt).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    NativeEEAFrame.backward_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change Multiset.map (AlgorithmGate.oracleFreeEvent .empty) _ = _
  have eventId : AlgorithmGate.oracleFreeEvent .empty = id := by
    funext event
    cases event with
    | classicalOperation impossible => cases impossible
    | classicalQuery impossible => cases impossible
    | oracle impossible => cases impossible
    | gate _ => rfl
    | preparation _ => rfl
    | measurement _ => rfl
  rw [eventId, Multiset.map_id]
  exact forward_cost modulus prime

private theorem forward_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (forward modulus prime).Path) :
    (forward modulus prime).resourcePool path ≤ NativeBudget.inPlace modulus.size := by
  have pool : (forward modulus prime).resourcePool path =
      (NativeEEAFrame.forward modulus prime).eventCost :=
    native_pool modulus.size (NativeEEAFrame.forward modulus prime) path
  exact (pool.trans (forward_cost modulus prime)).le.trans
    (NativeBudget.inPlace_bound modulus prime.one_lt)

private theorem backward_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (backward modulus prime).Path) :
    (backward modulus prime).resourcePool path ≤ NativeBudget.inPlace modulus.size := by
  have pool : (backward modulus prime).resourcePool path =
      (NativeEEAFrame.backward modulus prime).eventCost :=
    native_pool modulus.size (NativeEEAFrame.backward modulus prime) path
  exact (pool.trans (backward_cost modulus prime)).le.trans
    (NativeBudget.inPlace_bound modulus prime.one_lt)

private theorem product_budget (modulus : Nat) (path : (product modulus).Path) :
    (product modulus).resourcePool path ≤ VariableGidney.nativeBudget modulus.size := by
  have pool : (product modulus).resourcePool path =
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)).eventCost :=
    native_pool modulus.size _ path
  exact pool.le.trans (NativeProductFrame.nativeProductFrame_budget _ _)

private theorem swap_budget (width : Nat) (path : (swap width).Path) :
    (swap width).resourcePool path ≤
      (3 * width) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := by
  have pool : (swap width).resourcePool path = (FrameSwap.program width).eventCost :=
    native_pool width (FrameSwap.program width) path
  refine pool.le.trans ?_
  apply ResourcePool.le_scaled_of_support_card_le
  · intro focus present
    change focus ∈ (EncodedBit.GateSpec.programList
      (QubitLayout.canonical (ProductPlacement.frameEncoding width).width) .empty
      (EncodedBit.Word.swapGates (FramePorts.accumulator width) (FramePorts.numerator width)
        (FrameSwap.separation width))).eventCost at present
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      EncodedBit.GateSpec.programList_eventTrace] at present
    have listed : focus ∈ (EncodedBit.Word.swapGates (FramePorts.accumulator width)
        (FramePorts.numerator width) (FrameSwap.separation width)).map
          (EncodedBit.GateSpec.event .empty) :=
      present
    obtain ⟨gate, member, rfl⟩ := List.mem_map.mp listed
    have cnot := EncodedBit.Word.swapGates_isCnot (FramePorts.accumulator width)
      (FramePorts.numerator width) (FrameSwap.separation width) gate member
    cases gate with
    | x target => cases cnot
    | cnot control target distinct =>
        simp [EncodedBit.GateSpec.event, EncodedBit.GateSpec.primitive,
          QubitPrimitive.event, QubitPrimitive.nativeToken,
          AlgorithmGate.model, AlgorithmGate.coordinate, ResourcePool.singleton]
    | toffoli first second target different separateFirst separateSecond => cases cnot
  · exact (FrameSwap.frameSwap_event_count width).le

/-- Each real path satisfies the independent coordinatewise native allowance. -/
theorem body_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) :
    (body modulus prime).resourcePool path ≤ bodyBudget modulus.size := by
  change ResourcePool.ofList ((forward modulus prime).eventTrace path.1 ++
    ((product modulus).eventTrace path.2.1 ++
      ((NumeratorReset.code modulus.size).eventTrace path.2.2.1 ++
        ((backward modulus prime).eventTrace path.2.2.2.1 ++
          ((NumeratorCorrection.code modulus.size
              (InPlaceArithmetic.modulusWord modulus)).eventTrace path.2.2.2.2.1 ++
            (swap modulus.size).eventTrace path.2.2.2.2.2))))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add (forward_budget modulus prime path.1)
    (add_le_add (product_budget modulus path.2.1)
      (add_le_add (NumeratorReset.code_budget modulus.size path.2.2.1)
        (add_le_add (backward_budget modulus prime path.2.2.2.1)
          (add_le_add (NumeratorCorrection.code_budget _ _ path.2.2.2.2.1)
            (swap_budget modulus.size path.2.2.2.2.2)))))

/-- Allocation retains every zero-preparation and seed-loading event before the body. -/
theorem eventTrace (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).eventTrace path =
      ZeroPreparation.eventTrace AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size) ++
      (InPlacePreparation.loadProgram modulus).eventTrace .empty .empty ++
      (body modulus prime).eventTrace path.2.2 := by
  change (InPlacePreparation.circuit modulus).eventTrace path.1 ++
    ((NumeratorMeasurement.allocate modulus.size).eventTrace path.2.1 ++ _) = _
  have allocation : (NumeratorMeasurement.allocate modulus.size).eventTrace path.2.1 = [] :=
    MeasurementCells.allocate_eventTrace _ _ _ _
  rw [InPlacePreparation.circuit_eventTrace, allocation, List.nil_append, List.append_assoc]

/-- The entire actual circuit obeys the independent preparation and native-coordinate budget. -/
theorem event_budget (modulus : Nat) (prime : Nat.Prime modulus)
  (path : (code modulus prime).Path) :
    (code modulus prime).resourcePool path ≤ events modulus := by
  change ResourcePool.ofList ((code modulus prime).eventTrace path) ≤ _
  rw [eventTrace, ResourcePool.ofList_append, ResourcePool.ofList_append]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
    (InputPreparation.auxiliaryLayout modulus.size) +
      ResourcePool.ofList (InPlacePreparation.loadProgram modulus).eventTrace +
      (body modulus prime).resourcePool path.2.2 ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, load_pool]
  change (ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
      EncodedBit.Word.BasisLoad.xCount (InPlacePreparation.loadConstant modulus) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit)) +
      (body modulus prime).resourcePool path.2.2 ≤
    (ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
      EncodedBit.Word.BasisLoad.xCount (InPlacePreparation.loadConstant modulus) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit)) + bodyBudget modulus.size
  exact add_le_add le_rfl (body_budget modulus prime path.2.2)

private theorem native_depth (width : Nat)
    (member : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    (path : (NumeratorRuntime.code width member).Path) :
    (NumeratorRuntime.code width member).depth (fun _ => 1) path ≤
      ((NumeratorRuntime.code width member).resourcePool path).card := by
  change (NumeratorRuntime.program width member).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [NumeratorReset.placement_depth, native_pool]
  exact ShiftResources.unitDepth_le_count member

private theorem correction_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (path : (NumeratorCorrection.code width modulus).Path) :
    (NumeratorCorrection.code width modulus).depth (fun _ => 1) path ≤
      (NativeProductCorrection.nativeBudget width).card :=
  (native_depth width (NumeratorCorrection.member width modulus path.1) path.2).trans
      (Multiset.card_le_card (NumeratorCorrection.code_budget width modulus path))

private theorem body_depth (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) :
    (body modulus prime).depth (fun _ => 1) path ≤ bodyDepth modulus.size := by
  have forwardBound := (native_depth modulus.size (NativeEEAFrame.forward modulus prime)
    path.1).trans (Multiset.card_le_card (forward_budget modulus prime path.1))
  change (forward modulus prime).depth (fun _ => 1) path.1 ≤
    (NativeBudget.inPlace modulus.size).card at forwardBound
  have productBound := (native_depth modulus.size
    (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))
    path.2.1).trans
      (Multiset.card_le_card (product_budget modulus path.2.1))
  change (product modulus).depth (fun _ => 1) path.2.1 ≤
    (VariableGidney.nativeBudget modulus.size).card at productBound
  have backwardBound := (native_depth modulus.size (NativeEEAFrame.backward modulus prime)
    path.2.2.2.1).trans (Multiset.card_le_card (backward_budget modulus prime path.2.2.2.1))
  change (backward modulus prime).depth (fun _ => 1) path.2.2.2.1 ≤
    (NativeBudget.inPlace modulus.size).card at backwardBound
  have swapBound : (swap modulus.size).depth (fun _ => 1) path.2.2.2.2.2 = 3 * modulus.size := by
    change (NumeratorRuntime.program modulus.size
      (FrameSwap.program modulus.size)).evaluatedEventDepth (fun _ => 1) = _
    exact (NumeratorReset.placement_depth modulus.size
      (FrameSwap.program modulus.size) (fun _ => 1)).trans
        (FrameSwap.frameSwap_depth modulus.size)
  have resetBound := NumeratorReset.code_depth modulus.size path.2.2.1
  have correctionBound := correction_depth modulus.size (InPlaceArithmetic.modulusWord modulus)
    path.2.2.2.2.1
  change (forward modulus prime).depth (fun _ => 1) path.1 +
    ((product modulus).depth (fun _ => 1) path.2.1 +
      ((NumeratorReset.code modulus.size).depth (fun _ => 1) path.2.2.1 +
        ((backward modulus prime).depth (fun _ => 1) path.2.2.2.1 +
          ((NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus)).depth
              (fun _ => 1) path.2.2.2.2.1 +
            (swap modulus.size).depth (fun _ => 1) path.2.2.2.2.2)))) ≤ _
  unfold bodyDepth
  omega

/-- The same actual circuit obeys the serial bound including preparation and feed-forward. -/
theorem depth (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).depth (fun _ => 1) path ≤ depthBound modulus.size := by
  change DepthExpr.depthEval (fun _ => 1)
      (ZeroPreparation.eventDepth AlgorithmGate.model .empty
        (InputPreparation.auxiliaryLayout modulus.size)) +
    (InPlacePreparation.loadProgram modulus).evaluatedEventDepth (fun _ => 1) +
    ((NumeratorMeasurement.allocate modulus.size).depth (fun _ => 1) path.2.1 +
      (body modulus prime).depth (fun _ => 1) path.2.2) ≤ _
  have allocation : (NumeratorMeasurement.allocate modulus.size).depth
      (fun _ => 1) path.2.1 = 0 := MeasurementCells.allocate_depth _ _ _ _ _
  rw [ZeroPreparation.zeroPreparation_unit_depth, allocation, Nat.zero_add]
  have zeroBound :
      (if InputPreparation.auxiliaryWidth modulus.size = 0 then 0 else 1) ≤ 1 := by
    split_ifs <;> omega
  have loaded := load_depth modulus
  have bodyBound := body_depth modulus prime path.2.2
  unfold depthBound
  omega

/-- The final context has exactly n finite result bits beside the full original quantum frame. -/
theorem context_resident (width : Nat) :
    (NumeratorMeasurement.context width).residentSpace = space width := by
  rw [NumeratorMeasurement.context_space, InverseResources.after_resident]
  rfl

/-- All live entries have the owned or retained role and contribute to the auxiliary pool too. -/
theorem context_auxiliary (width : Nat) :
    (NumeratorMeasurement.context width).auxiliarySpace = space width := by
  rw [NumeratorMeasurement.context, MeasurementCells.context_auxiliarySpace,
    InverseResources.after_auxiliary]
  rfl

private theorem body_visited (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (body modulus prime).visitedContexts path) :
    frame = NumeratorMeasurement.context modulus.size := by
  change frame ∈ [_] ++ ([_] ++
    ((NumeratorReset.code modulus.size).visitedContexts path.2.2.1 ++
      ([_] ++ ([_] ++ [_])))) at present
  rw [NumeratorReset.visited] at present
  simpa using present

private theorem after_le_resident (width : Nat) :
    (InversePreparation.after width).residentSpace ≤ space width := by
  rw [← context_resident]
  exact MeasurementCells.context_residentSpace_mono (InversePreparation.after width) 2
    (Nat.zero_le width)

private theorem after_le_auxiliary (width : Nat) :
    (InversePreparation.after width).auxiliarySpace ≤ space width := by
  rw [← context_auxiliary]
  exact MeasurementCells.context_auxiliarySpace_mono (InversePreparation.after width) 2
    (Nat.zero_le width)

/-- Every actual allocation and execution context fits the independently specified full capacity. -/
theorem resident (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).peakResidentSpace path ≤ space modulus.size := by
  refine (Circuit.peakResidentSpace_seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [InPlacePreparation.circuit_resident]
    apply SpacePool.max_le
    · refine le_trans ?_ (after_le_resident modulus.size)
      rw [InverseResources.before_resident, InverseResources.after_resident]
      exact InverseResources.input_le modulus.size
    · exact after_le_resident modulus.size
  · refine (Circuit.peakResidentSpace_seq (NumeratorMeasurement.allocate modulus.size)
      (body modulus prime) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (MeasurementCells.allocate_peakResidentSpace _ _ _ path.2.1).trans
        (context_resident modulus.size).le
    · apply Circuit.peakResidentSpace_le_of_visited
      intro frame present
      rw [body_visited modulus prime path.2.2 frame present, context_resident]

/-- Auxiliary accounting follows the same actual path and includes every retained outcome cell. -/
theorem auxiliary (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).peakAuxiliarySpace path ≤ space modulus.size := by
  refine (Circuit.peakAuxiliarySpace_seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [InPlacePreparation.circuit_auxiliary]
    apply SpacePool.max_le
    · refine le_trans ?_ (after_le_auxiliary modulus.size)
      rw [InverseResources.before_auxiliary, InverseResources.after_auxiliary]
      exact InverseResources.input_le modulus.size
    · exact after_le_auxiliary modulus.size
  · refine (Circuit.peakAuxiliarySpace_seq (NumeratorMeasurement.allocate modulus.size)
      (body modulus prime) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (MeasurementCells.allocate_peakAuxiliarySpace _ _ _ path.2.1).trans
        (context_auxiliary modulus.size).le
    · apply Circuit.peakAuxiliarySpace_le_of_visited
      intro frame present
      rw [body_visited modulus prime path.2.2 frame present, context_auxiliary]

end

end QuantumAlg.MeasuredUncompute.InPlaceDivisionResources
