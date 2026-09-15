/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Resources.Unitary
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Actual fixed-count finite-cyclic sampling resources

One original three-register bank is prepared once. Every exponent readout is
stored directly in its own retained finite cell. Only later samples reset the
same bank: each wire executes three events, while the independent pool records
both correction alternatives and the prescribed shift. All samples and the
complete bank remain live in the returned output. The two inverse Fourier
circuits retain their original parallel depth.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Original literal Algorithm-1 preparations, one encoded query and both inverse QFTs. -/
def unitaryEnvelope (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) : ResourcePool .quantum :=
  (B.algorithm1Circuit.eventCost + B.algorithm1Circuit.eventCost) +
    (ResourcePool.singleton (uxEvent P) +
      ((QFTCircuit (orderWidth P)).eventCost + (QFTCircuit (orderWidth P)).eventCost))

/-- Every exponent position contributes its actual finite Z measurement. -/
def sampleEnvelope (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) : ResourcePool .quantum :=
  unitaryEnvelope P B + sampleWidth P • ResourcePool.singleton (Circuit.zEvent 2)

private def resetStageEnvelope (dimension : ℕ+) (value : Fin dimension) :
    ResourcePool .quantum :=
  ResourcePool.singleton (Circuit.zEvent dimension) +
    (ResourcePool.ofList (List.ofFn fun amount : Fin dimension =>
      Resource.Event.gate (QuditShift.gateLabel amount)) +
        ResourcePool.singleton (.gate (QuditShift.gateLabel value)))

/-- Each original wire retains both correction alternatives and its encoded-identity shift. -/
def resetEnvelope (P : KnownOrderProblem G) (ux : UxAccess P) : ResourcePool .quantum :=
  ∑ index, resetStageEnvelope 2 ((Native.preparation P ux).value index)

/-- Every later slot pays for a complete bank reset before its original sample. -/
def reusedSampleEnvelope (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    ResourcePool .quantum := resetEnvelope P ux + sampleEnvelope P B

/-- Original parallel critical path followed by every sequential exponent readout. -/
def sampleDepthLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) : Nat :=
  B.depthBound + 1 +
    (orderWidth P + orderWidth P * (orderWidth P - 1) / 2 + orderWidth P / 2) + sampleWidth P

/-- Three actual reset dependencies per wire precede the original sample depth. -/
def reusedSampleDepthLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) : Nat :=
  3 * totalQubits P + sampleDepthLimit P B

/-- One complete original bank and all distinct raw finite result cells survive. -/
def samplingSpace (P : KnownOrderProblem G) (count : Nat) : SpacePool .quantum :=
  (count * sampleWidth P) • SpacePool.ofShape (.finite 2) +
    SpacePool.ofQuantumLayout (bankLayout P)

/-- The zero-count program still prepares its bank; subsequent slots pay explicit reset. -/
def eventBudget (P : KnownOrderProblem G) (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P) (count : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (Native.preparation P ux).event +
    (count • sampleEnvelope P B + (count - 1) • resetEnvelope P ux)

/-- Actual selected reset branches are counted separately from the larger alternative pool. -/
def eventCountLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (count : Nat) : Nat :=
  1 + count * (sampleEnvelope P B).card + (count - 1) * (3 * totalQubits P)

/-- Independent complete depth retains the original member's parallel inverse QFTs. -/
def depthLimit (P : KnownOrderProblem G)
    (B : UniformSuperposition.BinaryExpansion P.order) (count : Nat) : Nat :=
  1 + count * sampleDepthLimit P B + (count - 1) * (3 * totalQubits P)

private theorem resetStageEnvelope_card (dimension : ℕ+) (value : Fin dimension) :
    (resetStageEnvelope dimension value).card = dimension + 2 := by
  simp only [resetStageEnvelope, Multiset.card_add, ResourcePool.singleton,
    Multiset.card_replicate, ResourcePool.ofList, Multiset.coe_card, List.length_ofFn]
  omega

/-- Two correction alternatives are recorded, while the prescribed shift occurs only once. -/
theorem nativeFiniteCyclicBatch_resetEnvelope_card (P : KnownOrderProblem G) (ux : UxAccess P) :
    (resetEnvelope P ux).card = 4 * totalQubits P := by
  rw [resetEnvelope, Multiset.card_sum]
  calc
    _ = ∑ _ : Fin (totalQubits P), 4 :=
      Finset.sum_congr rfl (fun index _ => resetStageEnvelope_card 2 ((Native.preparation P
        ux).value index))
    _ = _ := by simp [mul_comm]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (P : KnownOrderProblem G) (count : Nat) (slot : Fin count)

private theorem context_width : (context base noQuantum P count).systemCount = totalQubits P := by
  have same := congrArg List.length (nativeFiniteCyclicBatch_context_wires base noQuantum P count)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using same

private theorem readouts_events
    (path : (Circuit.measurementSequence (readouts base noQuantum P count slot)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum P count slot)).eventTrace path =
      List.replicate (sampleWidth P) (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_eventTrace, readouts, List.map_ofFn]
  simp only [nativeFiniteCyclic_context_qubits P (nativeFiniteCyclicBatch_context_wires base
    noQuantum P count)]
  exact List.ofFn_const _ _

/-- Actual sampling preserves the original unitary trace and appends its real finite readouts. -/
theorem nativeFiniteCyclicBatch_sample_eventTrace (B : UniformSuperposition.BinaryExpansion
    P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    (sample base noQuantum P count B ux slot).eventTrace path =
      (GateLevelAttempt.quantumCircuit P B ux).eventTrace ++
        List.replicate (sampleWidth P) (Circuit.zEvent 2) := by
  change (member base noQuantum P count B ux).eventTrace ++
    (Circuit.measurementSequence (readouts base noQuantum P count slot)).eventTrace path.2 = _
  rw [readouts_events]
  simp only [member, UnitaryCircuit.reindex_eventTrace]

/-- The complete literal sample has exactly its independently specified event pool. -/
theorem nativeFiniteCyclicBatch_sample_pool
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    (sample base noQuantum P count B ux slot).resourcePool path = sampleEnvelope P B := by
  rw [Circuit.resourcePool, nativeFiniteCyclicBatch_sample_eventTrace,
    ResourcePool.ofList_append, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    GateLevelAttempt.quantumCircuit_eventCost,
    inverseQFTCircuit_eventCost_eq_pair, ResourcePool.ofList_replicate]
  rfl

/-- The real sample count is bounded by the same independent native allowance. -/
theorem nativeFiniteCyclicBatch_sample_eventCount_le (B : UniformSuperposition.BinaryExpansion
    P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    ((sample base noQuantum P count B ux slot).eventTrace path).length ≤ (sampleEnvelope P B).card
      :=
  Multiset.card_le_card (nativeFiniteCyclicBatch_sample_pool base noQuantum P count slot B ux
    path).le

/-- Original parallel member depth is retained before the sequential finite readouts. -/
theorem nativeFiniteCyclicBatch_sample_depth_le (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    (sample base noQuantum P count B ux slot).depth (fun _ => 1) path ≤ sampleDepthLimit P B := by
  change (member base noQuantum P count B ux).evaluatedEventDepth (fun _ => 1) +
    (Circuit.measurementSequence (readouts base noQuantum P count slot)).depth (fun _ => 1) path.2
      ≤ _
  rw [Circuit.measurementSequence_unitDepth, readouts, List.length_ofFn]
  simp only [member, UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.reindex_eventDepth]
  exact Nat.add_le_add_right
    (GateLevelAttempt.quantumCircuit_evaluatedEventDepth_one_le P B ux) _

private theorem resetStage_pool_le {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (QuditShift.resetWireToBasis wire output value).Path) :
    (QuditShift.resetWireToBasis wire output value).resourcePool path ≤
      resetStageEnvelope (ctx.quantumLayout.wire wire).dimension value := by
  rw [QuditShift.resetWireToBasis_pool]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero, resetStageEnvelope]
  apply add_le_add le_rfl
  apply add_le_add _ le_rfl
  change ({_} : Multiset (Resource.Event .quantum)) ≤
    ↑(List.ofFn fun amount : Fin (ctx.quantumLayout.wire wire).dimension =>
      Resource.Event.gate (QuditShift.gateLabel amount))
  exact Multiset.singleton_le.mpr (List.mem_ofFn.mpr ⟨_, rfl⟩)

private theorem resetStage_eq {left right : ℕ+} (a : Fin left) (b : Fin right)
    (dimensions : left = right) (values : a.val = b.val) :
    resetStageEnvelope left a = resetStageEnvelope right b := by
  subst right
  cases Fin.ext values
  rfl

private theorem wire_value (basis : (context base noQuantum P count).register.Index)
    (index : Fin (totalQubits P)) :
    (basis (wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) index)).val =
      ((layout P).binaryIndexEquiv.symm
        (basisEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) basis)
          index).val := by
  let correspondence := Execution.basisOfEqualWires (bankLayout P)
    (context base noQuantum P count).quantumLayout
    (layoutWires P (nativeFiniteCyclicBatch_context_wires base noQuantum P count))
  have value := Execution.basisOfEqualWires_value (bankLayout P)
    (context base noQuantum P count).quantumLayout
    (layoutWires P (nativeFiniteCyclicBatch_context_wires base noQuantum P count))
    (correspondence.symm basis) index
  change (correspondence (correspondence.symm basis)
    (wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)
      index)).val = _ at value
  rw [Equiv.apply_symm_apply] at value
  have inverse := Equiv.symm_apply_apply (layout P).binaryIndexEquiv
    (correspondence.symm basis)
  exact value.trans (congrArg
    (fun source : (layout P).toQuantumLayout.Basis => (source index).val) inverse).symm

private theorem reset_label_value (ux : UxAccess P) (index : Fin (totalQubits P)) :
    (resetLabel base noQuantum P count ux
      (wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count) index)).val =
        ((Native.preparation P ux).value index).val := by
  rw [wire_value]
  simp only [resetLabel, Equiv.apply_symm_apply]
  rfl

/-- Each correction belongs to the original wire's alternatives, with one prescribed shift. -/
theorem nativeFiniteCyclicBatch_reset_pool_le (ux : UxAccess P) (path : (reset base noQuantum P
    count ux slot).Path) :
    (reset base noQuantum P count ux slot).resourcePool path ≤ resetEnvelope P ux := by
  let correspondence := wireEquiv P (nativeFiniteCyclicBatch_context_wires base noQuantum P count)
  let budgets := fun index => resetStageEnvelope
    ((context base noQuantum P count).quantumLayout.wire index).dimension
      (resetLabel base noQuantum P count ux index)
  have bounded := Circuit.forRange_pool_le_sum (context base noQuantum P count).systemCount
    (fun index => QuditShift.resetWireToBasis index (resetCell base noQuantum P count slot index)
      (resetLabel base noQuantum P count ux index)) budgets
    (fun index => resetStage_pool_le index (resetCell base noQuantum P count slot index)
      (resetLabel base noQuantum P count ux index)) path
  refine bounded.trans_eq ?_
  rw [← correspondence.sum_comp budgets]
  apply Finset.sum_congr rfl
  intro index _
  exact resetStage_eq _ _
    (nativeFiniteCyclic_context_qubits P (nativeFiniteCyclicBatch_context_wires base noQuantum P
      count) _)
    (reset_label_value base noQuantum P count ux index)

/-- Only the selected correction executes: every original wire contributes exactly three events. -/
theorem nativeFiniteCyclicBatch_reset_eventCount (ux : UxAccess P) (path : (reset base noQuantum P
    count ux slot).Path) :
    ((reset base noQuantum P count ux slot).eventTrace path).length = 3 * totalQubits P := by
  exact (QuditShift.resetToBasis_eventCount (resetCell base noQuantum P count slot)
    (resetLabel base noQuantum P count ux) path).trans (congrArg (3 * ·) (context_width base
      noQuantum P count))

/-- Reset, measured correction and prescribed shift have three actual sequential dependencies. -/
theorem nativeFiniteCyclicBatch_reset_depth (ux : UxAccess P) (path : (reset base noQuantum P
    count ux slot).Path) :
    (reset base noQuantum P count ux slot).depth (fun _ => 1) path = 3 * totalQubits P := by
  exact (QuditShift.resetToBasisOn_unitDepth _ id (resetCell base noQuantum P count slot)
    (resetLabel base noQuantum P count ux) path).trans (congrArg (3 * ·) (context_width base
      noQuantum P count))

/-- The complete existing-bank reset precedes every reused sample's native envelope. -/
theorem nativeFiniteCyclicBatch_reusedSample_pool_le (B : UniformSuperposition.BinaryExpansion
    P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    (reusedSample base noQuantum P count B ux slot).resourcePool path ≤ reusedSampleEnvelope P B
      ux := by
  change ResourcePool.ofList ((reset base noQuantum P count ux slot).eventTrace path.1 ++
    (sample base noQuantum P count B ux slot).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (nativeFiniteCyclicBatch_reset_pool_le base noQuantum P count slot ux path.1)
    (nativeFiniteCyclicBatch_sample_pool base noQuantum P count slot B ux path.2).le

/-- The actual path counts selected reset corrections, independently of the larger event pool. -/
theorem nativeFiniteCyclicBatch_reusedSample_eventCount_le (B :
    UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    ((reusedSample base noQuantum P count B ux slot).eventTrace path).length ≤
      3 * totalQubits P + (sampleEnvelope P B).card := by
  change ((reset base noQuantum P count ux slot).eventTrace path.1 ++
    (sample base noQuantum P count B ux slot).eventTrace path.2).length ≤ _
  rw [List.length_append, nativeFiniteCyclicBatch_reset_eventCount]
  exact Nat.add_le_add_left (nativeFiniteCyclicBatch_sample_eventCount_le base noQuantum P count
    slot B ux path.2) _

/-- The original literal member critical path follows the whole-bank reset dependencies. -/
theorem nativeFiniteCyclicBatch_reusedSample_depth_le (B : UniformSuperposition.BinaryExpansion
    P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    (reusedSample base noQuantum P count B ux slot).depth (fun _ => 1) path ≤
      reusedSampleDepthLimit P B := by
  change (reset base noQuantum P count ux slot).depth (fun _ => 1) path.1 +
    (sample base noQuantum P count B ux slot).depth (fun _ => 1) path.2 ≤ _
  rw [nativeFiniteCyclicBatch_reset_depth]
  exact Nat.add_le_add_left (nativeFiniteCyclicBatch_sample_depth_le base noQuantum P count slot B
    ux path.2) _

/-- Actual retained-cell allocation adds no event to the one original basis preparation. -/
theorem nativeFiniteCyclicBatch_allocate_events (ux : UxAccess P) (path : (allocate base noQuantum
    P count ux).Path) :
    (allocate base noQuantum P count ux).eventTrace path = [(Native.preparation P ux).event] := by
  change [(Native.preparation P ux).event] ++
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth P)).eventTrace
      path.2 = _
  erw [MeasurementCells.allocate_eventTrace]
  rfl

/-- One actual preparation is the entire initialization native depth. -/
theorem nativeFiniteCyclicBatch_allocate_depth (ux : UxAccess P) (path : (allocate base noQuantum
    P count ux).Path) :
    (allocate base noQuantum P count ux).depth (fun _ => 1) path = 1 := by
  change 1 + (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth
    P)).depth
    (fun _ => 1) path.2 = _
  erw [MeasurementCells.allocate_depth]

/-- All outcome cells and the complete bank are added to the caller's residents. -/
theorem nativeFiniteCyclicBatch_context_residentSpace : (context base noQuantum P
    count).residentSpace =
    samplingSpace P count + base.residentSpace := by
  simp only [context, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, samplingSpace, add_assoc]

/-- Every newly owned bank and retained cell is auxiliary as well as resident. -/
theorem nativeFiniteCyclicBatch_context_auxiliarySpace : (context base noQuantum P
    count).auxiliarySpace =
    samplingSpace P count + base.auxiliarySpace := by
  simp only [context, MeasurementCells.context_auxiliarySpace, bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, samplingSpace, add_assoc]

/-- The real initialization never exceeds its complete final sampling frame. -/
theorem nativeFiniteCyclicBatch_allocate_resident (ux : UxAccess P) (path : (allocate base
    noQuantum P count ux).Path) :
    (allocate base noQuantum P count ux).peakResidentSpace path ≤
      (context base noQuantum P count).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  change frame ∈ [base, bankContext base noQuantum P] ++
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth
      P)).visitedContexts
      path.2 at present
  rcases List.mem_append.mp present with earlier | later
  · rcases List.mem_cons.mp earlier with first | second
    · subst frame
      rw [nativeFiniteCyclicBatch_context_residentSpace]
      exact fun _ => Nat.le_add_left _ _
    · have same := List.mem_singleton.mp second
      subst frame
      exact MeasurementCells.context_residentSpace_mono _ 2 (Nat.zero_le (count * sampleWidth P))
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts _ _ _ _ _ later
    exact MeasurementCells.context_residentSpace_mono _ 2 bounded

/-- The actual initialization counts every new bank and cell in its auxiliary peak. -/
theorem nativeFiniteCyclicBatch_allocate_auxiliary (ux : UxAccess P) (path : (allocate base
    noQuantum P count ux).Path) :
    (allocate base noQuantum P count ux).peakAuxiliarySpace path ≤
      (context base noQuantum P count).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  change frame ∈ [base, bankContext base noQuantum P] ++
    (MeasurementCells.allocate (bankContext base noQuantum P) 2 (count * sampleWidth
      P)).visitedContexts
      path.2 at present
  rcases List.mem_append.mp present with earlier | later
  · rcases List.mem_cons.mp earlier with first | second
    · subst frame
      rw [nativeFiniteCyclicBatch_context_auxiliarySpace]
      exact fun _ => Nat.le_add_left _ _
    · have same := List.mem_singleton.mp second
      subst frame
      exact MeasurementCells.context_auxiliarySpace_mono _ 2 (Nat.zero_le (count * sampleWidth P))
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts _ _ _ _ _ later
    exact MeasurementCells.context_auxiliarySpace_mono _ 2 bounded

private theorem sample_visited (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P) (path : (sample base noQuantum P count B ux slot).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈ (sample base noQuantum P count B ux slot).visitedContexts path) :
    frame = context base noQuantum P count := by
  change frame ∈ [context base noQuantum P count] ++
    (Circuit.measurementSequence (readouts base noQuantum P count slot)).visitedContexts path.2
      at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  rcases List.mem_append.mp present with first | later
  · exact List.mem_singleton.mp first
  · exact (List.mem_replicate.mp later).2

/-- Each real sample has the exact independently counted original member and finite readouts. -/
theorem nativeFiniteCyclicBatch_sample_eventCount
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    ((sample base noQuantum P count B ux slot).eventTrace path).length =
      (sampleEnvelope P B).card :=
  congrArg Multiset.card (nativeFiniteCyclicBatch_sample_pool base noQuantum P count slot B ux path)

/-- A reused sample executes one selected correction per wire, with no sample copy or pack. -/
theorem nativeFiniteCyclicBatch_reusedSample_eventCount
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    ((reusedSample base noQuantum P count B ux slot).eventTrace path).length =
      3 * totalQubits P + (sampleEnvelope P B).card := by
  change ((reset base noQuantum P count ux slot).eventTrace path.1 ++
    (sample base noQuantum P count B ux slot).eventTrace path.2).length = _
  rw [List.length_append, nativeFiniteCyclicBatch_reset_eventCount,
    nativeFiniteCyclicBatch_sample_eventCount]

/-- Sampling visits the complete existing resident frame without allocating or releasing entries. -/
theorem nativeFiniteCyclicBatch_sample_resident
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    (sample base noQuantum P count B ux slot).peakResidentSpace path =
      (context base noQuantum P count).residentSpace := by
  apply le_antisymm
  · apply Circuit.peakResidentSpace_le_of_visited
    intro frame present
    rw [sample_visited base noQuantum P count slot B ux path frame present]
  · exact Circuit.input_residentSpace_le_peak _ path

/-- The reset uses an existing sample cell and retains the same full resident frame. -/
theorem nativeFiniteCyclicBatch_reusedSample_resident
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    (reusedSample base noQuantum P count B ux slot).peakResidentSpace path =
      (context base noQuantum P count).residentSpace := by
  dsimp only [reusedSample] at path ⊢
  rw [Circuit.peakResidentSpace_seq]
  dsimp only [reset]
  erw [QuditShift.resetToBasis_resident, nativeFiniteCyclicBatch_sample_resident,
    SpacePool.max_self]

/-- Sampling visits the complete existing auxiliary frame without allocating or releasing entries.
-/
theorem nativeFiniteCyclicBatch_sample_auxiliary
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sample base noQuantum P count B ux slot).Path) :
    (sample base noQuantum P count B ux slot).peakAuxiliarySpace path =
      (context base noQuantum P count).auxiliarySpace := by
  apply le_antisymm
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro frame present
    rw [sample_visited base noQuantum P count slot B ux path frame present]
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- The reset uses an existing sample cell and retains the same full auxiliary frame. -/
theorem nativeFiniteCyclicBatch_reusedSample_auxiliary
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (reusedSample base noQuantum P count B ux slot).Path) :
    (reusedSample base noQuantum P count B ux slot).peakAuxiliarySpace path =
      (context base noQuantum P count).auxiliarySpace := by
  dsimp only [reusedSample] at path ⊢
  rw [Circuit.peakAuxiliarySpace_seq]
  dsimp only [reset]
  erw [QuditShift.resetToBasis_auxiliary, nativeFiniteCyclicBatch_sample_auxiliary,
    SpacePool.max_self]

private theorem range_eventCount {ctx : RuntimeCtx .quantum} (amount count : Nat)
    (body : Fin count → Circuit ctx ctx)
    (same : ∀ index path, ((body index).eventTrace path).length = amount)
    (path : (Circuit.forRange count body).Path) :
    ((Circuit.forRange count body).eventTrace path).length = count * amount := by
  induction count with
  | zero => simp [Circuit.forRange, Circuit.eventTrace]
  | succ count ih =>
      change ((body 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2).length = _
      rw [List.length_append, same, ih _ (fun index => same index.succ), Nat.succ_mul]
      omega

private theorem batch_pool (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sampleBatch base noQuantum P B ux count).Path) :
    (sampleBatch base noQuantum P B ux count).resourcePool path ≤
      count • sampleEnvelope P B + (count - 1) • resetEnvelope P ux := by
  cases count with
  | zero => exact le_rfl
  | succ count =>
      change ResourcePool.ofList
        ((sample base noQuantum P (count + 1) B ux 0).eventTrace path.1 ++
          (Circuit.forRange count (fun index =>
            reusedSample base noQuantum P (count + 1) B ux index.succ)).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      have first := (nativeFiniteCyclicBatch_sample_pool base noQuantum P
        (count + 1) 0 B ux path.1).le
      have later := Circuit.forRange_pool_le count
        (fun index => reusedSample base noQuantum P (count + 1) B ux index.succ)
        (reusedSampleEnvelope P B ux)
        (fun index => nativeFiniteCyclicBatch_reusedSample_pool_le base noQuantum P
          (count + 1) index.succ B ux) path.2
      simpa only [Circuit.resourcePool, ResourcePool.scale, reusedSampleEnvelope,
        smul_add, add_nsmul,
        one_nsmul, Nat.add_sub_cancel, add_assoc, add_left_comm, add_comm]
        using add_le_add first later

private theorem batch_eventCount (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P) (path : (sampleBatch base noQuantum P B ux count).Path) :
    ((sampleBatch base noQuantum P B ux count).eventTrace path).length =
      count * (sampleEnvelope P B).card + (count - 1) * (3 * totalQubits P) := by
  cases count with
  | zero => simp [sampleBatch, Circuit.eventTrace]
  | succ count =>
      change ((sample base noQuantum P (count + 1) B ux 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index =>
          reusedSample base noQuantum P (count + 1) B ux index.succ)).eventTrace path.2).length = _
      rw [List.length_append, nativeFiniteCyclicBatch_sample_eventCount,
        range_eventCount _ count _ (fun index => nativeFiniteCyclicBatch_reusedSample_eventCount
          base noQuantum P (count + 1) index.succ B ux)]
      simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.mul_add, one_mul]
      omega

private theorem batch_depth (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (sampleBatch base noQuantum P B ux count).Path) :
    (sampleBatch base noQuantum P B ux count).depth (fun _ => 1) path ≤
      count * sampleDepthLimit P B + (count - 1) * (3 * totalQubits P) := by
  cases count with
  | zero => exact Nat.zero_le _
  | succ count =>
      change (sample base noQuantum P (count + 1) B ux 0).depth (fun _ => 1) path.1 +
        (Circuit.forRange count (fun index =>
          reusedSample base noQuantum P (count + 1) B ux index.succ)).depth (fun _ => 1) path.2 ≤ _
      have first := nativeFiniteCyclicBatch_sample_depth_le base noQuantum P
        (count + 1) 0 B ux path.1
      have later := Circuit.forRange_depth_le count
        (fun index => reusedSample base noQuantum P (count + 1) B ux index.succ)
        (reusedSampleDepthLimit P B)
        (fun index => nativeFiniteCyclicBatch_reusedSample_depth_le base noQuantum P
          (count + 1) index.succ B ux) path.2
      simp only [reusedSampleDepthLimit, totalQubits, Nat.mul_add] at later
      simp only [totalQubits, Nat.add_sub_cancel, Nat.add_mul, one_mul]
      nlinarith [first, later]

private theorem batch_resident (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P) (path : (sampleBatch base noQuantum P B ux count).Path) :
    (sampleBatch base noQuantum P B ux count).peakResidentSpace path ≤
      (context base noQuantum P count).residentSpace := by
  cases count with
  | zero => exact (SpacePool.max_zero _).le
  | succ count =>
      refine (Circuit.peakResidentSpace_seq _ _ path).le.trans ?_
      exact SpacePool.max_le
        (nativeFiniteCyclicBatch_sample_resident base noQuantum P (count + 1) 0 B ux path.1).le
        (Circuit.forRange_resident_le count
          (fun index => reusedSample base noQuantum P (count + 1) B ux index.succ)
          _ le_rfl (fun index path =>
            (nativeFiniteCyclicBatch_reusedSample_resident base noQuantum P
              (count + 1) index.succ B ux path).le) path.2)

private theorem batch_auxiliary (B : UniformSuperposition.BinaryExpansion P.order)
    (ux : UxAccess P) (path : (sampleBatch base noQuantum P B ux count).Path) :
    (sampleBatch base noQuantum P B ux count).peakAuxiliarySpace path ≤
      (context base noQuantum P count).auxiliarySpace := by
  cases count with
  | zero => exact (SpacePool.max_zero _).le
  | succ count =>
      refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans ?_
      exact SpacePool.max_le
        (nativeFiniteCyclicBatch_sample_auxiliary base noQuantum P (count + 1) 0 B ux path.1).le
        (Circuit.forRange_auxiliary_le count
          (fun index => reusedSample base noQuantum P (count + 1) B ux index.succ)
          _ le_rfl (fun index path =>
            (nativeFiniteCyclicBatch_reusedSample_auxiliary base noQuantum P
              (count + 1) index.succ B ux path).le) path.2)

/-- Every complete actual sample path meets the independent preparation, sample and reset pool. -/
theorem nativeFiniteCyclicBatch_run_pool_le
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    (run base noQuantum P count B ux).code.resourcePool path ≤ eventBudget P B ux count := by
  change ResourcePool.ofList ((allocate base noQuantum P count ux).eventTrace path.1 ++
    (sampleBatch base noQuantum P B ux count).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, nativeFiniteCyclicBatch_allocate_events]
  exact add_le_add le_rfl (batch_pool base noQuantum P count B ux path.2)

/-- The same full path counts actual corrections and all literal member events exactly. -/
theorem nativeFiniteCyclicBatch_run_eventCount
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    ((run base noQuantum P count B ux).code.eventTrace path).length =
      eventCountLimit P B count := by
  change ((allocate base noQuantum P count ux).eventTrace path.1 ++
    (sampleBatch base noQuantum P B ux count).eventTrace path.2).length = _
  rw [List.length_append, nativeFiniteCyclicBatch_allocate_events, batch_eventCount]
  simp only [List.length_singleton, eventCountLimit, Nat.add_assoc]

/-- Complete depth retains original parallel member evaluation and every paid sequential reset. -/
theorem nativeFiniteCyclicBatch_run_depth_le
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    (run base noQuantum P count B ux).code.depth (fun _ => 1) path ≤ depthLimit P B count := by
  change (allocate base noQuantum P count ux).depth (fun _ => 1) path.1 +
    (sampleBatch base noQuantum P B ux count).depth (fun _ => 1) path.2 ≤ _
  rw [nativeFiniteCyclicBatch_allocate_depth]
  simpa only [depthLimit, Nat.add_assoc] using
    Nat.add_le_add_left (batch_depth base noQuantum P count B ux path.2) 1

/-- Every returned sample and the complete bank contribute to the exact actual resident peak. -/
theorem nativeFiniteCyclicBatch_run_resident
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    (run base noQuantum P count B ux).code.peakResidentSpace path =
      samplingSpace P count + base.residentSpace := by
  rw [← nativeFiniteCyclicBatch_context_residentSpace base noQuantum P count]
  apply le_antisymm
  · refine (Circuit.peakResidentSpace_seq _ _ path).le.trans ?_
    exact SpacePool.max_le
      (nativeFiniteCyclicBatch_allocate_resident base noQuantum P count ux path.1)
      (batch_resident base noQuantum P count B ux path.2)
  · exact Circuit.output_residentSpace_le_peak _ path

/-- Every returned sample and the complete bank contribute to the exact actual auxiliary peak. -/
theorem nativeFiniteCyclicBatch_run_auxiliary
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    (run base noQuantum P count B ux).code.peakAuxiliarySpace path =
      samplingSpace P count + base.auxiliarySpace := by
  rw [← nativeFiniteCyclicBatch_context_auxiliarySpace base noQuantum P count]
  apply le_antisymm
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans ?_
    exact SpacePool.max_le
      (nativeFiniteCyclicBatch_allocate_auxiliary base noQuantum P count ux path.1)
      (batch_auxiliary base noQuantum P count B ux path.2)
  · exact Circuit.output_auxiliarySpace_le_peak _ path

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
