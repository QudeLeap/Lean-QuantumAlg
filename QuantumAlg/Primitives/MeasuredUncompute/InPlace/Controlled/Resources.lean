/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Runtime
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled

/-!
# Resources of the actual controlled measured arithmetic body

Quantum control is lowered to literal X, CNOT and Toffoli instructions.
The independent pools charge this expansion, both H-CNOT-H phase corrections,
the unconditional reset, and the final three-CNOT swap. One real owned control
augments the original three-word frame, without another field bank, and all
finite measurement cells remain live. The actual body allocates nothing
[LYL+26, sec_point_add/sec_point_add.tex:24-36,52-121].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceControlled

noncomputable section

open Execution MAU.Inversion.SharedEEA MAU.Multiplication
open ProductPlacement EncodedBit GateSpec

-- Resource composition uses certified list interfaces rather than evaluating arithmetic lists.
attribute [local irreducible] NativeEEAFrame.backwardGates NativeReusedEEA.forwardGates
  WorkspaceReuse.placement

/-- Complete live storage includes the real coherent control and all retained measurement cells. -/
def space (width : Nat) : SpacePool .quantum :=
  width • SpacePool.ofShape (.finite 2) + OwnedQubits.space (3 * width + 4 * width.size + 12)

private def controlledBudget (count : Nat) (active : Bool) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  count • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot) +
    (4 * count) • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli) +
    (if active then 0 else 2) •
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)

private def copyBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  width • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli) +
    2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)

private def maskBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  width • (2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit) +
    ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot))

private def saveBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  controlledBudget (VariableGidney.eventBound width) true + copyBudget width

private def correctionBudget (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  2 • VariableGidney.nativeBudget width + 2 • maskBudget width +
    2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)

/-- Independent event allowance before the one real unconditional measurement sequence. -/
def beforeBudget (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  match operation with
  | .division => controlledBudget (ForwardResources.inPlaceBound width) true + saveBudget width
  | .multiplication => saveBudget width

/-- Independent event allowance for the actual stored correction and full final swap. -/
def afterBudget (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  match operation with
  | .division => controlledBudget (ForwardResources.inPlaceBound width) true +
      (correctionBudget width +
        (3 * width) • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot))
  | .multiplication => controlledBudget (ForwardResources.inPlaceBound width) true +
      (correctionBudget width +
        (controlledBudget (ForwardResources.inPlaceBound width) true +
          (3 * width) • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)))

/-- All allowances are independent width formulas, in the same three-block execution order. -/
def events (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  beforeBudget operation width + (NumeratorReset.budget width + afterBudget operation width)

/-- Both controlled arithmetic arms reserve the same one-qubit coordinate. -/
lemma events_singleQubit_count (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (events operation width) =
      4 + 6 * width + 2 * VariableGidney.eventBound width := by
  cases operation <;>
    simp [events, beforeBudget, afterBudget, saveBudget, correctionBudget,
      controlledBudget, copyBudget, maskBudget, NumeratorReset.budget,
      VariableGidney.nativeBudget_singleQubit_count, Circuit.zEvent] <;> omega

/-- Division and multiplication differ in control placement, but reserve equal CNOT totals. -/
lemma events_cnot_count (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (events operation width) =
      2 * ForwardResources.inPlaceBound width +
        3 * VariableGidney.eventBound width + 5 * width := by
  cases operation <;>
    simp [events, beforeBudget, afterBudget, saveBudget, correctionBudget,
      controlledBudget, copyBudget, maskBudget, NumeratorReset.budget,
      VariableGidney.nativeBudget_cnot_count, Circuit.zEvent] <;> omega

/-- Both arithmetic arms reserve equal Toffoli totals despite different control order. -/
lemma events_toffoli_count (operation : InPlaceTarget.Operation) (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (events operation width) =
      8 * ForwardResources.inPlaceBound width +
        6 * VariableGidney.eventBound width + width := by
  cases operation <;>
    simp [events, beforeBudget, afterBudget, saveBudget, correctionBudget,
      controlledBudget, copyBudget, maskBudget, NumeratorReset.budget,
      VariableGidney.nativeBudget_toffoli_count, Circuit.zEvent] <;> omega

/-- Serial dependence includes H, all Z writes, and the selected reset before the final
correction. -/
def depthBound (operation : InPlaceTarget.Operation) (width : Nat) : Nat :=
  (beforeBudget operation width).card + ((1 + 2 * width) + (afterBudget operation width).card)

private lemma copy_cost (width : Nat) :
    (controlled width false (copyGates width)).eventCost = copyBudget width := by
  have counts :
      ((NativeFrameControl.gates width false (copyGates width)).map xMultiplicity).sum = 2 ∧
      ((NativeFrameControl.gates width false (copyGates width)).map cnotMultiplicity).sum = 0 ∧
      ((NativeFrameControl.gates width false (copyGates width)).map toffoliMultiplicity).sum =
        width := by
    simpa [NativeFrameControl.lifted, copyGates, Word.xorIntoGates,
      List.map_ofFn, Function.comp_def, GateSpec.prodLeft, xMultiplicity,
      cnotMultiplicity, toffoliMultiplicity] using
      NativeFrameControl.nativeFrameControl_counts width false (copyGates width)
  apply Multiset.ext.mpr
  intro focus
  change ResourcePool.count focus (programList (nativeLayout width) .empty
    (NativeFrameControl.gates width false (copyGates width))).eventCost = _
  by_cases single : focus = .gate .singleQubit
  · subst focus
    rw [programList_x_count_eq_sum]
    rw [show ((NativeFrameControl.gates width false (copyGates width)).map
      xMultiplicity).sum = 2 from counts.1]
    simp [copyBudget, ResourcePool.singleton]
  by_cases cnot : focus = .gate .cnot
  · subst focus
    rw [programList_cnot_count_eq_sum]
    rw [show ((NativeFrameControl.gates width false (copyGates width)).map
      cnotMultiplicity).sum = 0 from counts.2.1]
    simp [copyBudget, ResourcePool.singleton]
  by_cases toffoli : focus = .gate .toffoli
  · subst focus
    rw [programList_toffoli_count_eq_sum]
    rw [show ((NativeFrameControl.gates width false (copyGates width)).map
      toffoliMultiplicity).sum = width from counts.2.2]
    simp [copyBudget, ResourcePool.singleton]
  have outside : focus ∉ primitiveAlphabet := by
    simpa [primitiveAlphabet, ResourcePool.ofList] using And.intro single (And.intro cnot toffoli)
  rw [programList_count_zero_of_not_mem_primitiveAlphabet _ _ _ outside]
  simp [copyBudget, ResourcePool.singleton, single, toffoli]

private lemma controlled_bound (width : Nat) (active : Bool)
    (source : List (GateSpec (frameEncoding width))) (count : Nat)
    (bounded : source.length ≤ count) :
    (controlled width active source).eventCost ≤ controlledBudget count active := by
  have counts := NativeFrameControl.nativeFrameControl_counts width active source
  have sourceLength := length_eq_multiplicity_sums (NativeFrameControl.lifted width source)
  have liftedBound : (NativeFrameControl.lifted width source).length ≤ count := by
    simpa only [NativeFrameControl.lifted, List.length_map] using bounded
  apply ResourcePool.le_iff_count.mpr
  intro focus
  by_cases single : focus = .gate .singleQubit
  · subst focus
    change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      (programList (nativeLayout width) .empty
        (NativeFrameControl.gates width active source)).eventCost ≤ _
    rw [programList_x_count_eq_sum, counts.1]
    cases active <;> simp [controlledBudget, ResourcePool.count_singleton]
  by_cases cnot : focus = .gate .cnot
  · subst focus
    change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)
      (programList (nativeLayout width) .empty
        (NativeFrameControl.gates width active source)).eventCost ≤ _
    rw [programList_cnot_count_eq_sum, counts.2.1]
    simp only [controlledBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton, ↓reduceIte, mul_one]
    change ((NativeFrameControl.lifted width source).map xMultiplicity).sum ≤ count
    omega
  by_cases toffoli : focus = .gate .toffoli
  · subst focus
    change ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.toffoli)
      (programList (nativeLayout width) .empty
        (NativeFrameControl.gates width active source)).eventCost ≤ _
    rw [programList_toffoli_count_eq_sum, counts.2.2]
    simp only [controlledBudget, ResourcePool.count_add, ResourcePool.count_nsmul,
      ResourcePool.count_singleton, ↓reduceIte, mul_one]
    omega
  have outside : focus ∉ primitiveAlphabet := by
    simpa [primitiveAlphabet, ResourcePool.ofList] using And.intro single (And.intro cnot toffoli)
  change ResourcePool.count focus (programList (nativeLayout width) .empty
    (NativeFrameControl.gates width active source)).eventCost ≤ _
  rw [programList_count_zero_of_not_mem_primitiveAlphabet _ _ _ outside]
  exact Nat.zero_le _

private lemma forward_length_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (NativeEEAFrame.forwardGates modulus prime).length ≤
      ForwardResources.inPlaceBound modulus.size := by
  have count := ForwardResources.inPlace_count modulus prime.one_lt
  rw [← InPlaceDivisionResources.forward_cost modulus prime] at count
  simpa only [NativeEEAFrame.forward, programList_eventCost_card] using count

private lemma backward_length_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (NativeEEAFrame.backwardGates modulus prime).length ≤
      ForwardResources.inPlaceBound modulus.size := by
  simpa only [NativeEEAFrame.backwardGates, List.length_map, List.length_reverse] using
    forward_length_bound modulus prime

private lemma forward_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (forward modulus prime).eventCost ≤
      controlledBudget (ForwardResources.inPlaceBound modulus.size) true :=
  controlled_bound modulus.size true _ _ (forward_length_bound modulus prime)

private lemma backward_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (backward modulus prime).eventCost ≤
      controlledBudget (ForwardResources.inPlaceBound modulus.size) true :=
  controlled_bound modulus.size true _ _ (backward_length_bound modulus prime)

private lemma reused_cost_bound (modulus : Nat) (prime : Nat.Prime modulus) :
    (reusedForward modulus prime).eventCost ≤
      controlledBudget (ForwardResources.inPlaceBound modulus.size) true := by
  have same : (reusedForward modulus prime).eventCost =
      (backward modulus prime).eventCost := by
    rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
      ← UnitaryCircuit.ofList_eventTrace_eq_eventCost]
    simp only [reusedForward, backward,
      NativeEEAFrame.Controlled.nativeEEAControlled_reusedForward_trace,
      NativeEEAFrame.Controlled.nativeEEAControlled_backward_trace,
      NativeEEAFrame.Controlled.reusedForwardGates, List.map_reverse,
      ResourcePool.ofList, Multiset.coe_reverse]
  have bound := backward_cost_bound modulus prime
  exact same.le.trans bound

private lemma seq_cost_bound (width : Nat) (first second : NativeCircuit width)
    (left right : ResourcePool (.quantum AlgorithmGate.model .empty))
    (firstBound : first.eventCost ≤ left) (secondBound : second.eventCost ≤ right) :
    (first.seq second).eventCost ≤ left + right :=
  (UnitaryCircuit.seq_eventCost first second).le.trans (add_le_add firstBound secondBound)

private lemma save_cost_bound (modulus : Nat) :
    (save modulus).eventCost ≤ saveBudget modulus.size := by
  have active := controlled_bound modulus.size true
    (NativeProductFrame.gates modulus.size (InPlaceArithmetic.modulusWord modulus))
    (VariableGidney.eventBound modulus.size)
    (NativeProductFrame.nativeProductFrame_gates_length_bound _ _)
  dsimp only [controlled, NativeFrameControl.program, NativeFrameControl.gates] at active
  change (programList (nativeLayout modulus.size) .empty
    (NativeProductFrame.Controlled.gates modulus.size
      (InPlaceArithmetic.modulusWord modulus))).eventCost ≤ _ at active
  exact seq_cost_bound modulus.size _ _ _ _ active (copy_cost modulus.size).le

private lemma selected_mask_budget (width : Nat) (mask : Fin width → Bool) :
    (Word.PhaseCorrection.selected mask).length •
      (2 • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
        (.gate AlgorithmGate.Coordinate.singleQubit) +
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot)) ≤ maskBudget width := by
  apply ResourcePool.le_iff_count.mpr
  intro focus
  rw [maskBudget, ResourcePool.count_nsmul, ResourcePool.count_nsmul]
  exact Nat.mul_le_mul_right _
    (Word.PhaseCorrection.phaseCorrection_selected_count_le mask)

private lemma correction_compute_budget (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    ResourcePool.ofList ((ReusedProduct.Controlled.computeGates width modulus).map
      (event .empty)) ≤ VariableGidney.nativeBudget width := by
  have trace : (ReusedProduct.Controlled.computeGates width modulus).map (event .empty) =
      (NativeProductFrame.program width modulus).eventTrace := by
    rw [ReusedProduct.Controlled.computeGates, map_event_prodLeft]
    simp only [List.map_map, Function.comp_def, FullPlacement.placeGate_event]
    exact NativeProductFrame.nativeProductFrame_gates_trace width modulus
  rw [trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]
  exact NativeProductFrame.nativeProductFrame_budget width modulus

private lemma correction_cost_bound (modulus : Nat)
    (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (correction modulus value).eventCost ≤ correctionBudget modulus.size := by
  have arithmetic := correction_compute_budget modulus.size (InPlaceArithmetic.modulusWord modulus)
  have selected := selected_mask_budget modulus.size (QubitReadouts.mask value)
  have bound := add_le_add (add_le_add (add_le_add arithmetic selected) arithmetic)
    (add_le_add selected (le_refl (2 • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty) (.gate AlgorithmGate.Coordinate.singleQubit))))
  rw [correction, UnitaryCircuit.seq_eventCost,
    ReusedProduct.Controlled.reusedProductControlled_cost, inactiveCorrection,
    Word.PhaseCorrection.Controlled.program,
    Word.PhaseCorrection.Controlled.controlledPhaseCorrection_sequence_cost]
  simp only [if_true, add_zero, ResourcePool.ofList, Multiset.coe_reverse]
  convert bound using 1
  · rfl
  · rw [correctionBudget, two_nsmul, two_nsmul]
    abel

private lemma swap_cost_bound (width : Nat) :
    (swap width).eventCost ≤
      (3 * width) • ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
      (.gate AlgorithmGate.Coordinate.cnot) := by
  have actual : (swap width).eventCost = (FrameSwap.program width).eventCost := by
    exact (UnitaryCircuit.ofList_eventTrace_eq_eventCost (swap width)).symm.trans
      ((congrArg ResourcePool.ofList (uncontrolled_trace width (FrameSwap.program width))).trans
        (UnitaryCircuit.ofList_eventTrace_eq_eventCost (FrameSwap.program width)))
  have oldPool := InPlaceDivisionResources.native_pool width (FrameSwap.program width) ()
  exact actual.le.trans (oldPool.symm.le.trans (InPlaceDivisionResources.swap_budget width ()))

/-- The native prefix's literal events meet the independently prescribed controlled coordinates. -/
lemma beforeReset_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) :
    (beforeReset operation modulus prime).eventCost ≤ beforeBudget operation modulus.size := by
  cases operation
  · exact save_cost_bound modulus
  · exact seq_cost_bound modulus.size _ _ _ _
      (forward_cost_bound modulus prime) (save_cost_bound modulus)

/-- Every actual stored vector selects a suffix within the same independent native allowance. -/
lemma suffix_budget (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (value : CShape.Value (.fixedVector modulus.size (.finite 2))) :
    (suffix operation modulus prime value).eventCost ≤ afterBudget operation modulus.size := by
  have reused := reused_cost_bound modulus prime
  have backwardBound := backward_cost_bound modulus prime
  have correctionBound := correction_cost_bound modulus value
  have swapBound := swap_cost_bound modulus.size
  cases operation
  · exact seq_cost_bound modulus.size _ _ _ _ reused
      (seq_cost_bound modulus.size _ _ _ _ correctionBound
        (seq_cost_bound modulus.size _ _ _ _
          backwardBound swapBound))
  · exact seq_cost_bound modulus.size _ _ _ _ backwardBound
      (seq_cost_bound modulus.size _ _ _ _
        correctionBound swapBound)

private lemma native_pool {allowAllocation : Bool} (width : Nat)
    (program : NativeCircuit width)
    (path : (nativeCode width program allowAllocation).Path) :
    (nativeCode width program allowAllocation).resourcePool path = program.eventCost := by
  change ResourcePool.ofList (runtimeProgram width program).eventTrace = _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost, runtimeProgram_cost]

private lemma numeratorReset_budget (width : Nat)
    (path : (NumeratorReset.code width false).Path) :
    (NumeratorReset.code width false).resourcePool path ≤ NumeratorReset.budget width := by
  have first := NumeratorReset.hadamard_cost width path.1
  change ResourcePool.ofList
    (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).eventTrace = _ at first
  have measured := Circuit.measurementSequence_qubit_resourcePool (allowAllocation := false)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := .empty) (classicalOracles := .empty) (NumeratorMeasurement.readouts width)
    (by
      intro item present
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
      exact NumeratorMeasurement.wire_dimension width index) path.2.1
  have measuredExact :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).resourcePool path.2.1 =
      width • ResourcePool.singleton
        (Circuit.zEvent (gates := AlgorithmGate.model) (oracles := .empty) 2 .empty .empty) := by
    simpa only [NumeratorMeasurement.readouts, QubitReadouts.readouts, List.length_ofFn]
      using measured
  have last := NumeratorReset.reset_budget width path.2.2
  change ResourcePool.ofList
    (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).eventTrace ≤ _
      at last
  change ResourcePool.ofList
    ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).eventTrace ++
      ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).eventTrace path.2.1 ++
        (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).eventTrace)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add first.le (add_le_add measuredExact.le last)

private lemma reset_budget {allowAllocation : Bool} (width : Nat) (path : (reset width
    allowAllocation).Path) :
    (reset width allowAllocation).resourcePool path ≤ NumeratorReset.budget width := by
  exact (Circuit.resourcePool_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongUnion (NumeratorMeasurement.context width)
      (controlContext width) (control_disjoint width))
    (NumeratorReset.code width false) path).le.trans
      (numeratorReset_budget width path)

/-- Each path of the actual emitted body pays its complete controlled and measured event pool. -/
lemma body_budget {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime allowAllocation).Path) :
    (body operation modulus prime allowAllocation).resourcePool path ≤ events operation
      modulus.size := by
  change ResourcePool.ofList
    ((nativeCode modulus.size (beforeReset operation modulus prime) allowAllocation).eventTrace
      path.1 ++
      ((reset modulus.size allowAllocation).eventTrace path.2.1 ++
        (selectedSuffix operation modulus prime allowAllocation).eventTrace path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add ((native_pool (allowAllocation := allowAllocation) _ _ _).le.trans
    (beforeReset_budget operation modulus prime))
    (add_le_add (reset_budget (allowAllocation := allowAllocation) modulus.size path.2.1)
      ((native_pool (allowAllocation := allowAllocation) _ _ _).le.trans (suffix_budget operation
        modulus prime path.2.2.1)))

private lemma native_depth {allowAllocation : Bool} (width : Nat)
    (program : NativeCircuit width)
    (path : (nativeCode width program allowAllocation).Path) :
    (nativeCode width program allowAllocation).depth (fun _ => 1) path ≤ program.eventCost.card
      := by
  change (runtimeProgram width program).evaluatedEventDepth (fun _ => 1) + 0 ≤ _
  rw [runtimeProgram, UnitaryCircuit.placeAt_evaluatedEventDepth, Nat.add_zero]
  exact ShiftResources.unitDepth_le_count program

private lemma numeratorReset_unitDepth (width : Nat)
    (path : (NumeratorReset.code width false).Path) :
    (NumeratorReset.code width false).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  have first :
      (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).evaluatedEventDepth
        (fun _ => 1) = if width = 0 then 0 else 1 := by
    rw [NumeratorReset.placement_depth]
    change (UnitaryCircuit.onBinarySuffix (encoding width).width
      (Gate.HadamardLayer.circuit .empty width)).evaluatedEventDepth (fun _ => 1) = _
    rw [UnitaryCircuit.unitaryCircuit_onBinarySuffix_evaluatedEventDepth]
    exact Gate.HadamardLayer.hadamardLayer_circuit_unit_depth .empty width
  have measured :
      (Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (NumeratorMeasurement.readouts width)).depth (fun _ => 1) path.2.1 = width :=
    (Circuit.measurementSequence_unitDepth (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (NumeratorMeasurement.readouts width)
      path.2.1).trans List.length_ofFn
  have last :
      (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).evaluatedEventDepth
        (fun _ => 1) ≤ if width = 0 then 0 else 1 := by
    rw [NumeratorReset.placement_depth]
    change (UnitaryCircuit.onCanonicalBinarySuffix (encoding width).width
      (NumeratorResetParallel.program (NumeratorReset.outcome path.2.2.1))).evaluatedEventDepth
        (fun _ => 1) ≤ _
    rw [UnitaryCircuit.onCanonicalBinarySuffix_evaluatedEventDepth]
    exact NumeratorResetParallel.program_unitDepth _
  change (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).evaluatedEventDepth
      (fun _ => 1) +
    ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (NumeratorMeasurement.readouts width)).depth (fun _ => 1) path.2.1 +
      (NumeratorRuntime.program width (NumeratorReset.member width path.2.2.1)).evaluatedEventDepth
        (fun _ => 1)) ≤ _
  rw [first, measured]
  split_ifs at * <;> omega

private lemma reset_depth {allowAllocation : Bool} (width : Nat) (path : (reset width
    allowAllocation).Path) :
    (reset width allowAllocation).depth (fun _ => 1) path ≤ 1 + 2 * width := by
  change (NumeratorReset.code width false).depth (fun _ => 1) path ≤ _
  exact numeratorReset_unitDepth width path

/-- The actual serial execution meets its independent native and feed-forward depth allowance. -/
lemma body_depth {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus)
    (path : (body operation modulus prime allowAllocation).Path) :
    (body operation modulus prime allowAllocation).depth (fun _ => 1) path ≤ depthBound operation
      modulus.size := by
  change (nativeCode modulus.size (beforeReset operation modulus prime) allowAllocation).depth
    (fun _ => 1) path.1 +
    ((reset modulus.size allowAllocation).depth (fun _ => 1) path.2.1 +
      (nativeCode modulus.size (suffix operation modulus prime path.2.2.1) allowAllocation).depth
        (fun _ => 1) path.2.2.2) ≤ _
  exact Nat.add_le_add
    ((native_depth (allowAllocation := allowAllocation) _ _ _).trans (Multiset.card_le_card
      (beforeReset_budget operation modulus
      prime)))
    (Nat.add_le_add (reset_depth (allowAllocation := allowAllocation) modulus.size path.2.1)
      ((native_depth (allowAllocation := allowAllocation) _ _ _).trans
        (Multiset.card_le_card (suffix_budget operation modulus prime path.2.2.1))))

/-- Actual event multiplicities also give the complete event-count allowance. -/
lemma body_event_count {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus :
    Nat) (prime :
    Nat.Prime modulus)
    (path : (body operation modulus prime allowAllocation).Path) :
    ((body operation modulus prime allowAllocation).eventTrace path).length ≤ (events operation
      modulus.size).card :=
  Multiset.card_le_card (body_budget (allowAllocation := allowAllocation) operation modulus prime
    path)

private lemma control_resident (width : Nat) :
    (controlContext width).residentSpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (controlQubitLayout width).toQuantumLayout_dimensionCount dimension

private lemma control_auxiliary (width : Nat) :
    (controlContext width).auxiliarySpace = OwnedQubits.space 1 := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      exact (controlQubitLayout width).toQuantumLayout_dimensionCount dimension

private lemma ownedSpace_add (left right : Nat) :
    OwnedQubits.space (left + right) = OwnedQubits.space left + OwnedQubits.space right := by
  funext axis
  cases axis with
  | classicalBits => rfl
  | quantumSystems dimension =>
      by_cases binary : (2 : ℕ+) = dimension <;> simp [OwnedQubits.space, binary]

private lemma one_control_space (width : Nat) :
    InPlaceDivisionResources.space width + OwnedQubits.space 1 = space width := by
  rw [InPlaceDivisionResources.space, add_assoc, ← ownedSpace_add]
  have count : 3 * width + 4 * width.size + 11 + 1 = 3 * width + 4 * width.size + 12 := by omega
  rw [count]
  rfl

/-- The complete actual context charges the additional owned control as exactly one qubit. -/
lemma context_resident (width : Nat) : (context width).residentSpace = space width := by
  rw [context, RuntimeCtx.residentSpace_disjointUnion,
    InPlaceDivisionResources.context_resident, control_resident]
  exact one_control_space width

lemma context_auxiliary (width : Nat) : (context width).auxiliarySpace = space width := by
  rw [context, RuntimeCtx.auxiliarySpace_disjointUnion,
    InPlaceDivisionResources.context_auxiliary, control_auxiliary]
  exact one_control_space width

/-- Every actual execution path keeps exactly the full three-word frame, control and finite cells.
-/
lemma body_resident {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus :
    Nat) (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime allowAllocation).Path) :
    (body operation modulus prime allowAllocation).peakResidentSpace path = space modulus.size := by
  have upper := (body operation modulus prime allowAllocation).peakResidentSpace_le_of_visited path
    (context modulus.size).residentSpace (by
      intro visited present
      have same : visited = context modulus.size := by
        simpa only [body_visited (allowAllocation := allowAllocation), List.mem_cons,
          List.not_mem_nil, or_false, or_self] using present
      rw [same])
  have lower := (body operation modulus prime allowAllocation).residentSpace_le_peak_of_visited path
    (context modulus.size) (by rw [body_visited (allowAllocation := allowAllocation)]; exact
      List.mem_cons_self)
  exact (le_antisymm upper lower).trans (context_resident modulus.size)

lemma body_auxiliary {allowAllocation : Bool} (operation : InPlaceTarget.Operation) (modulus :
    Nat) (prime : Nat.Prime
    modulus)
    (path : (body operation modulus prime allowAllocation).Path) :
    (body operation modulus prime allowAllocation).peakAuxiliarySpace path = space modulus.size
      := by
  have upper := (body operation modulus prime allowAllocation).peakAuxiliarySpace_le_of_visited path
    (context modulus.size).auxiliarySpace (by
      intro visited present
      have same : visited = context modulus.size := by
        simpa only [body_visited (allowAllocation := allowAllocation), List.mem_cons,
          List.not_mem_nil, or_false, or_self] using present
      rw [same])
  have lower := (body operation modulus prime allowAllocation).auxiliarySpace_le_peak_of_visited
    path
    (context modulus.size) (by rw [body_visited (allowAllocation := allowAllocation)]; exact
      List.mem_cons_self)
  exact (le_antisymm upper lower).trans (context_auxiliary modulus.size)

end

end QuantumAlg.MeasuredUncompute.InPlaceControlled
