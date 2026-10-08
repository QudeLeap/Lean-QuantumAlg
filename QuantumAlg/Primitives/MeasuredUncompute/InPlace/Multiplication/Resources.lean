/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Resources

/-!
# Independent resources of the actual measured in-place multiplication

The actual order is product, H/Z/reset, reused EEA forward, selected
recompute/Z/uncompute, the same reused EEA backward, and the actual swap
[LYL+26, sec_point_add/sec_point_add.tex:119-122]. Every native component
is charged, including the complete source-corrected shared EEA schedule.

The two measured arithmetic operations share the same independently
specified full frame capacity and the same native component allowances.
Only their real execution order differs. Reuse of those numeric allowances
below does not substitute division execution or its correctness theorem.
The actual trace, depth dependencies, preparation and retained finite
measurement cells are derived from this multiplication circuit itself.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceMultiplicationResources

noncomputable section

open Execution MAU.Inversion.SharedEEA MAU.Multiplication InPlaceMultiplication

/-- Independent component allowances in the actual multiplication execution order. -/
def bodyBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  VariableGidney.nativeBudget width +
    (NumeratorReset.budget width +
      (NativeBudget.inPlace width +
        (NativeProductCorrection.nativeBudget width +
          (NativeBudget.inPlace width +
            (3 * width) • ResourcePool.singleton
              (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)))))

/-- Per-wire zero preparation, fixed-seed X loading and multiplication are charged. -/
def events (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ZeroPreparation.eventCost AlgorithmGate.model .empty
      (InputPreparation.auxiliaryLayout modulus.size) +
    (EncodedBit.Word.BasisLoad.xCount (InPlacePreparation.loadConstant modulus) •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate .singleQubit)) +
    bodyBudget modulus.size

/-- All serial dependencies of the actual six-block multiplication body remain in the bound. -/
def bodyDepth (width : Nat) : Nat :=
  (VariableGidney.nativeBudget width).card +
    ((1 + 2 * width) +
      ((NativeBudget.inPlace width).card +
        ((NativeProductCorrection.nativeBudget width).card +
          ((NativeBudget.inPlace width).card + 3 * width))))

/-- Zero preparation and fixed X loading precede the measured native body. -/
def depthBound (width : Nat) : Nat :=
  1 + InputPreparation.auxiliaryWidth width + bodyDepth width

private theorem product_budget (modulus : Nat) (path : (product modulus).Path) :
    (product modulus).resourcePool path ≤ VariableGidney.nativeBudget modulus.size :=
  InPlaceDivisionResources.product_budget modulus path

private theorem forward_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (forward modulus prime).Path) :
    (forward modulus prime).resourcePool path ≤ NativeBudget.inPlace modulus.size := by
  have pool := InPlaceDivisionResources.native_pool modulus.size
    (NativeReusedEEA.forward modulus prime) path
  have cost : (NativeReusedEEA.forward modulus prime).eventCost =
      (InPlaceForward.program modulus prime.one_lt).eventCost :=
    (NativeReusedEEA.forward_cost modulus prime).trans
      (InPlaceDivisionResources.backward_cost modulus prime)
  exact pool.le.trans (cost.le.trans (NativeBudget.inPlace_bound modulus prime.one_lt))

private theorem backward_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (backward modulus prime).Path) :
    (backward modulus prime).resourcePool path ≤ NativeBudget.inPlace modulus.size :=
  InPlaceDivisionResources.backward_budget modulus prime path

private theorem swap_budget (width : Nat) (path : (swap width).Path) :
    (swap width).resourcePool path ≤
      (3 * width) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) :=
  InPlaceDivisionResources.swap_budget width path

/-- Every literal multiplication path fits the independently specified native coordinates. -/
theorem body_budget (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) :
    (body modulus prime).resourcePool path ≤ bodyBudget modulus.size := by
  change ResourcePool.ofList ((product modulus).eventTrace path.1 ++
    ((NumeratorReset.code modulus.size).eventTrace path.2.1 ++
      ((forward modulus prime).eventTrace path.2.2.1 ++
        ((NumeratorCorrection.code modulus.size
            (InPlaceArithmetic.modulusWord modulus)).eventTrace path.2.2.2.1 ++
          ((backward modulus prime).eventTrace path.2.2.2.2.1 ++
            (swap modulus.size).eventTrace path.2.2.2.2.2))))) ≤ _
  simp only [ResourcePool.ofList_append]
  exact add_le_add (product_budget modulus path.1)
    (add_le_add (NumeratorReset.code_budget modulus.size path.2.1)
      (add_le_add (forward_budget modulus prime path.2.2.1)
        (add_le_add (NumeratorCorrection.code_budget _ _ path.2.2.2.1)
          (add_le_add (backward_budget modulus prime path.2.2.2.2.1)
            (swap_budget modulus.size path.2.2.2.2.2)))))

/-- Finite-cell allocation retains all actual zero-preparation and seed X events. -/
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

/-- The actual full circuit satisfies its independent native-event budget on every path. -/
theorem event_budget (modulus : Nat) (prime : Nat.Prime modulus)
  (path : (code modulus prime).Path) :
    (code modulus prime).resourcePool path ≤ events modulus := by
  change ResourcePool.ofList ((code modulus prime).eventTrace path) ≤ _
  rw [eventTrace, ResourcePool.ofList_append, ResourcePool.ofList_append]
  change ZeroPreparation.eventCost AlgorithmGate.model .empty
    (InputPreparation.auxiliaryLayout modulus.size) +
      ResourcePool.ofList (InPlacePreparation.loadProgram modulus).eventTrace +
      (body modulus prime).resourcePool path.2.2 ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, InPlaceDivisionResources.load_pool]
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

private theorem body_depth (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) :
    (body modulus prime).depth (fun _ => 1) path ≤ bodyDepth modulus.size := by
  have productBound := (InPlaceDivisionResources.native_depth modulus.size
    (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus))
    path.1).trans (Multiset.card_le_card (product_budget modulus path.1))
  change (product modulus).depth (fun _ => 1) path.1 ≤
    (VariableGidney.nativeBudget modulus.size).card at productBound
  have forwardBound := (InPlaceDivisionResources.native_depth modulus.size
    (NativeReusedEEA.forward modulus prime)
    path.2.2.1).trans
        (Multiset.card_le_card (forward_budget modulus prime path.2.2.1))
  change (forward modulus prime).depth (fun _ => 1) path.2.2.1 ≤
    (NativeBudget.inPlace modulus.size).card at forwardBound
  have backwardBound := (InPlaceDivisionResources.native_depth modulus.size
    (NativeEEAFrame.backward modulus prime)
    path.2.2.2.2.1).trans
        (Multiset.card_le_card (backward_budget modulus prime path.2.2.2.2.1))
  change (backward modulus prime).depth (fun _ => 1) path.2.2.2.2.1 ≤
    (NativeBudget.inPlace modulus.size).card at backwardBound
  have swapBound : (swap modulus.size).depth (fun _ => 1) path.2.2.2.2.2 = 3 * modulus.size := by
    change (NumeratorRuntime.program modulus.size
      (FrameSwap.program modulus.size)).evaluatedEventDepth (fun _ => 1) = _
    exact (NumeratorReset.placement_depth modulus.size
      (FrameSwap.program modulus.size) (fun _ => 1)).trans
        (FrameSwap.frameSwap_depth modulus.size)
  have resetBound := NumeratorReset.code_depth modulus.size path.2.1
  have correctionBound := InPlaceDivisionResources.correction_depth modulus.size
    (InPlaceArithmetic.modulusWord modulus) path.2.2.2.1
  change (product modulus).depth (fun _ => 1) path.1 +
    ((NumeratorReset.code modulus.size).depth (fun _ => 1) path.2.1 +
      ((forward modulus prime).depth (fun _ => 1) path.2.2.1 +
        ((NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus)).depth
            (fun _ => 1) path.2.2.2.1 +
          ((backward modulus prime).depth (fun _ => 1) path.2.2.2.2.1 +
            (swap modulus.size).depth (fun _ => 1) path.2.2.2.2.2)))) ≤ _
  unfold bodyDepth
  omega

/-- Serial depth includes fixed preparation, reset and both result-dependent operations. -/
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
  have loaded := InPlaceDivisionResources.load_depth modulus
  have bodyBound := body_depth modulus prime path.2.2
  unfold depthBound
  omega

private theorem body_visited (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (body modulus prime).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (body modulus prime).visitedContexts path) :
    frame = NumeratorMeasurement.context modulus.size := by
  change frame ∈ [_] ++ ((NumeratorReset.code modulus.size).visitedContexts path.2.1 ++
    ([_] ++ ([_] ++ ([_] ++ [_])))) at present
  rw [NumeratorReset.visited] at present
  simpa using present

/-- Multiplication fits the same independently fixed three-word frame plus n retained cells. -/
theorem resident (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).peakResidentSpace path ≤ InPlaceDivisionResources.space modulus.size := by
  refine (Circuit.peakResidentSpace_seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [InPlacePreparation.circuit_resident]
    apply SpacePool.max_le
    · refine le_trans ?_ (InPlaceDivisionResources.after_le_resident modulus.size)
      rw [InverseResources.before_resident, InverseResources.after_resident]
      exact InverseResources.input_le modulus.size
    · exact InPlaceDivisionResources.after_le_resident modulus.size
  · refine (Circuit.peakResidentSpace_seq (NumeratorMeasurement.allocate modulus.size)
      (body modulus prime) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (MeasurementCells.allocate_peakResidentSpace _ _ _ path.2.1).trans
        (InPlaceDivisionResources.context_resident modulus.size).le
    · apply Circuit.peakResidentSpace_le_of_visited
      intro frame present
      rw [body_visited modulus prime path.2.2 frame present,
        InPlaceDivisionResources.context_resident]

/-- Every actual live owned bank and retained cell also appears in the auxiliary capacity. -/
theorem auxiliary (modulus : Nat) (prime : Nat.Prime modulus)
    (path : (code modulus prime).Path) :
    (code modulus prime).peakAuxiliarySpace path ≤ InPlaceDivisionResources.space modulus.size := by
  refine (Circuit.peakAuxiliarySpace_seq (InPlacePreparation.circuit modulus)
    (.seq (NumeratorMeasurement.allocate modulus.size) (body modulus prime)) path).le.trans ?_
  apply SpacePool.max_le
  · rw [InPlacePreparation.circuit_auxiliary]
    apply SpacePool.max_le
    · refine le_trans ?_ (InPlaceDivisionResources.after_le_auxiliary modulus.size)
      rw [InverseResources.before_auxiliary, InverseResources.after_auxiliary]
      exact InverseResources.input_le modulus.size
    · exact InPlaceDivisionResources.after_le_auxiliary modulus.size
  · refine (Circuit.peakAuxiliarySpace_seq (NumeratorMeasurement.allocate modulus.size)
      (body modulus prime) path.2).le.trans ?_
    apply SpacePool.max_le
    · exact (MeasurementCells.allocate_peakAuxiliarySpace _ _ _ path.2.1).trans
        (InPlaceDivisionResources.context_auxiliary modulus.size).le
    · apply Circuit.peakAuxiliarySpace_le_of_visited
      intro frame present
      rw [body_visited modulus prime path.2.2 frame present,
        InPlaceDivisionResources.context_auxiliary]

end

end QuantumAlg.MeasuredUncompute.InPlaceMultiplicationResources
