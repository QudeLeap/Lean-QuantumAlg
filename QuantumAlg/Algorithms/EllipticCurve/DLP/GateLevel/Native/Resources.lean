/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Readout
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Resources.Unitary
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Actual literal ECDLP sampling resources

The independent allowance contains the original two literal preparations,
one opaque group query, two inverse Fourier transforms and every real finite
readout. Reset uses each existing wire and an existing finite cell: three
actual operations, with both correction alternatives in its four-entry
qubit envelope. Prescribed shifts, including zero shifts, remain charged.
The original one-term order expansion is retained without a new premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The unchanged literal preparation, query and readout-member allowance. -/
def unitaryEnvelope (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    ResourcePool .quantum :=
  (GateLevelResources.orderPreparationEnvelope B +
    GateLevelResources.orderPreparationEnvelope B) +
      (ResourcePool.singleton (uPQEvent I) +
        ((QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost +
          (QFTCircuit (FiniteCyclicDLP.orderWidth (problem I))).eventCost))

/-- Each actual exponent wire contributes a finite Z readout, with no extra sample pack. -/
def sampleEnvelope (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    ResourcePool .quantum :=
  unitaryEnvelope I B + sampleWidth I • ResourcePool.singleton (Circuit.zEvent 2)

private def resetStageEnvelope (dimension : ℕ+) (value : Fin dimension) :
    ResourcePool .quantum :=
  ResourcePool.singleton (Circuit.zEvent dimension) +
    (ResourcePool.ofList (List.ofFn fun amount : Fin dimension =>
      Resource.Event.gate (QuditShift.gateLabel amount)) +
        ResourcePool.singleton (.gate (QuditShift.gateLabel value)))

/-- The original physical positions and prescribed basis determine the complete reset pool. -/
def resetEnvelope (I : ECDLPInstance E) : ResourcePool .quantum :=
  ∑ index, resetStageEnvelope 2 ((preparation I).value index)

/-- Every reused sample pays for the whole original bank reset before sampling. -/
def reusedSampleEnvelope (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) :
    ResourcePool .quantum := resetEnvelope I + sampleEnvelope I B

/-- Original critical-path depth followed by every real sequential finite measurement. -/
def sampleDepthLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) : Nat :=
  GateLevelResources.attemptDepthLimit I B + sampleWidth I

/-- Reset, correction and basis shift precede the original literal sample depth. -/
def reusedSampleDepthLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) : Nat :=
  3 * Layout.totalQubits I + sampleDepthLimit I B

/-- One complete original bank and all actual finite outcome cells remain resident. -/
def samplingSpace (I : ECDLPInstance E) : SpacePool .quantum :=
  sampleWidth I • SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout (bankLayout I)

private theorem resetStageEnvelope_card (dimension : ℕ+) (value : Fin dimension) :
    (resetStageEnvelope dimension value).card = dimension + 2 := by
  simp only [resetStageEnvelope, Multiset.card_add, ResourcePool.singleton,
    Multiset.card_replicate, ResourcePool.ofList, Multiset.coe_card, List.length_ofFn]
  omega

/-- Two correction alternatives are recorded, while the prescribed shift occurs only once. -/
theorem nativeECDLP_resetEnvelope_card (I : ECDLPInstance E) :
    (resetEnvelope I).card = 4 * Layout.totalQubits I := by
  rw [resetEnvelope, Multiset.card_sum]
  calc
    _ = ∑ _ : Fin (Layout.totalQubits I), 4 :=
      Finset.sum_congr rfl (fun index _ => resetStageEnvelope_card 2 ((preparation I).value index))
    _ = _ := by simp [mul_comm]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

private theorem context_width : (context base noQuantum I).systemCount = Layout.totalQubits I := by
  have same := congrArg List.length (nativeECDLP_context_wires base noQuantum I)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using same

private theorem readouts_events
    (path : (Circuit.measurementSequence (readouts base noQuantum I)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum I)).eventTrace path =
      List.replicate (sampleWidth I) (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_eventTrace, readouts, List.map_ofFn]
  simp only [nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I)]
  exact List.ofFn_const _ _

/-- Actual sampling preserves the original unitary trace and appends its real finite readouts. -/
theorem nativeECDLP_sample_eventTrace (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    (sample base noQuantum I B A).eventTrace path =
      (GateLevelAttempt.quantumCircuit I B A).eventTrace ++
        List.replicate (sampleWidth I) (Circuit.zEvent 2) := by
  change (member base noQuantum I B A).eventTrace ++
    (Circuit.measurementSequence (readouts base noQuantum I)).eventTrace path.2 = _
  rw [readouts_events]
  simp only [member, UnitaryCircuit.reindex_eventTrace]

/-- The literal one-term and multi-term preparations both fit the independent sample allowance. -/
theorem nativeECDLP_sample_pool_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    (sample base noQuantum I B A).resourcePool path ≤ sampleEnvelope I B := by
  rw [Circuit.resourcePool, nativeECDLP_sample_eventTrace, ResourcePool.ofList_append,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    GateLevelResources.quantumCircuit_eventCost,
    GateLevelResources.inverseQFTCircuit_eventCost_eq_pair, ResourcePool.ofList_replicate]
  have preparationBound :=
    GateLevelResources.paddedPreparation_eventCost_le_orderPreparationEnvelope I B
  exact add_le_add (add_le_add (add_le_add preparationBound preparationBound) le_rfl) le_rfl

/-- The real sample count is bounded by the same independent native allowance. -/
theorem nativeECDLP_sample_eventCount_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    ((sample base noQuantum I B A).eventTrace path).length ≤ (sampleEnvelope I B).card :=
  Multiset.card_le_card (nativeECDLP_sample_pool_le base noQuantum I B A path)

/-- Original parallel member depth is retained before the sequential finite readouts. -/
theorem nativeECDLP_sample_depth_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    (sample base noQuantum I B A).depth (fun _ => 1) path ≤ sampleDepthLimit I B := by
  change (member base noQuantum I B A).evaluatedEventDepth (fun _ => 1) +
    (Circuit.measurementSequence (readouts base noQuantum I)).depth (fun _ => 1) path.2 ≤ _
  rw [Circuit.measurementSequence_unitDepth, readouts, List.length_ofFn]
  simp only [member, UnitaryCircuit.evaluatedEventDepth, UnitaryCircuit.reindex_eventDepth]
  exact Nat.add_le_add_right
    (GateLevelResources.quantumCircuit_evaluatedEventDepth_one_le I B A) _

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

private theorem reset_label_value (index : Fin (Layout.totalQubits I)) :
    (resetLabel base noQuantum I
      (wireEquiv I (nativeECDLP_context_wires base noQuantum I) index)).val =
        ((preparation I).value index).val := by
  rw [wire_value]
  simp only [resetLabel, Equiv.apply_symm_apply]
  rfl

/-- Each correction belongs to the original wire's alternatives, with one prescribed shift. -/
theorem nativeECDLP_reset_pool_le (path : (reset base noQuantum I).Path) :
    (reset base noQuantum I).resourcePool path ≤ resetEnvelope I := by
  let correspondence := wireEquiv I (nativeECDLP_context_wires base noQuantum I)
  let budgets := fun index => resetStageEnvelope
    ((context base noQuantum I).quantumLayout.wire index).dimension
      (resetLabel base noQuantum I index)
  have bounded := Circuit.forRange_pool_le_sum (context base noQuantum I).systemCount
    (fun index => QuditShift.resetWireToBasis index (resetCell base noQuantum I index)
      (resetLabel base noQuantum I index)) budgets
    (fun index => resetStage_pool_le index (resetCell base noQuantum I index)
      (resetLabel base noQuantum I index)) path
  refine bounded.trans_eq ?_
  rw [← correspondence.sum_comp budgets]
  apply Finset.sum_congr rfl
  intro index _
  exact resetStage_eq _ _
    (nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I) _)
    (reset_label_value base noQuantum I index)

/-- Only the selected correction executes: every original wire contributes exactly three events. -/
theorem nativeECDLP_reset_eventCount (path : (reset base noQuantum I).Path) :
    ((reset base noQuantum I).eventTrace path).length = 3 * Layout.totalQubits I := by
  exact (QuditShift.resetToBasis_eventCount (resetCell base noQuantum I)
    (resetLabel base noQuantum I) path).trans (congrArg (3 * ·) (context_width base noQuantum I))

/-- Reset, measured correction and prescribed shift have three actual sequential dependencies. -/
theorem nativeECDLP_reset_depth (path : (reset base noQuantum I).Path) :
    (reset base noQuantum I).depth (fun _ => 1) path = 3 * Layout.totalQubits I := by
  exact (QuditShift.resetToBasisOn_unitDepth _ id (resetCell base noQuantum I)
    (resetLabel base noQuantum I) path).trans (congrArg (3 * ·) (context_width base noQuantum I))

/-- The complete existing-bank reset precedes every reused sample's native envelope. -/
theorem nativeECDLP_reusedSample_pool_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (reusedSample base noQuantum I B A).Path) :
    (reusedSample base noQuantum I B A).resourcePool path ≤ reusedSampleEnvelope I B := by
  change ResourcePool.ofList ((reset base noQuantum I).eventTrace path.1 ++
    (sample base noQuantum I B A).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (nativeECDLP_reset_pool_le base noQuantum I path.1)
    (nativeECDLP_sample_pool_le base noQuantum I B A path.2)

/-- The actual path counts selected reset corrections, independently of the larger event pool. -/
theorem nativeECDLP_reusedSample_eventCount_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (reusedSample base noQuantum I B A).Path) :
    ((reusedSample base noQuantum I B A).eventTrace path).length ≤
      3 * Layout.totalQubits I + (sampleEnvelope I B).card := by
  change ((reset base noQuantum I).eventTrace path.1 ++
    (sample base noQuantum I B A).eventTrace path.2).length ≤ _
  rw [List.length_append, nativeECDLP_reset_eventCount]
  exact Nat.add_le_add_left (nativeECDLP_sample_eventCount_le base noQuantum I B A path.2) _

/-- The original literal member critical path follows the whole-bank reset dependencies. -/
theorem nativeECDLP_reusedSample_depth_le (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (reusedSample base noQuantum I B A).Path) :
    (reusedSample base noQuantum I B A).depth (fun _ => 1) path ≤ reusedSampleDepthLimit I B := by
  change (reset base noQuantum I).depth (fun _ => 1) path.1 +
    (sample base noQuantum I B A).depth (fun _ => 1) path.2 ≤ _
  rw [nativeECDLP_reset_depth]
  exact Nat.add_le_add_left (nativeECDLP_sample_depth_le base noQuantum I B A path.2) _

/-- Actual retained-cell allocation adds no event to the one original basis preparation. -/
theorem nativeECDLP_allocate_events (path : (allocate base noQuantum I).Path) :
    (allocate base noQuantum I).eventTrace path = [(preparation I).event] := by
  change [(preparation I).event] ++
    (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I)).eventTrace
      path.2 = _
  erw [MeasurementCells.allocate_eventTrace]
  rfl

/-- One actual preparation is the entire initialization native depth. -/
theorem nativeECDLP_allocate_depth (path : (allocate base noQuantum I).Path) :
    (allocate base noQuantum I).depth (fun _ => 1) path = 1 := by
  change 1 + (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I)).depth
    (fun _ => 1) path.2 = _
  erw [MeasurementCells.allocate_depth]

/-- All outcome cells and the complete bank are added to the caller's residents. -/
theorem nativeECDLP_context_residentSpace : (context base noQuantum I).residentSpace =
    samplingSpace I + base.residentSpace := by
  simp only [context, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, samplingSpace, add_assoc]

/-- Every newly owned bank and retained cell is auxiliary as well as resident. -/
theorem nativeECDLP_context_auxiliarySpace : (context base noQuantum I).auxiliarySpace =
    samplingSpace I + base.auxiliarySpace := by
  simp only [context, MeasurementCells.context_auxiliarySpace, bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, samplingSpace, add_assoc]

/-- The real initialization never exceeds its complete final sampling frame. -/
theorem nativeECDLP_allocate_resident (path : (allocate base noQuantum I).Path) :
    (allocate base noQuantum I).peakResidentSpace path ≤
      (context base noQuantum I).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  change frame ∈ [base, bankContext base noQuantum I] ++
    (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I)).visitedContexts
      path.2 at present
  rcases List.mem_append.mp present with earlier | later
  · rcases List.mem_cons.mp earlier with first | second
    · subst frame
      rw [nativeECDLP_context_residentSpace]
      exact fun _ => Nat.le_add_left _ _
    · have same := List.mem_singleton.mp second
      subst frame
      exact MeasurementCells.context_residentSpace_mono _ 2 (Nat.zero_le (sampleWidth I))
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts _ _ _ _ _ later
    exact MeasurementCells.context_residentSpace_mono _ 2 bounded

/-- The actual initialization counts every new bank and cell in its auxiliary peak. -/
theorem nativeECDLP_allocate_auxiliary (path : (allocate base noQuantum I).Path) :
    (allocate base noQuantum I).peakAuxiliarySpace path ≤
      (context base noQuantum I).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  change frame ∈ [base, bankContext base noQuantum I] ++
    (MeasurementCells.allocate (bankContext base noQuantum I) 2 (sampleWidth I)).visitedContexts
      path.2 at present
  rcases List.mem_append.mp present with earlier | later
  · rcases List.mem_cons.mp earlier with first | second
    · subst frame
      rw [nativeECDLP_context_auxiliarySpace]
      exact fun _ => Nat.le_add_left _ _
    · have same := List.mem_singleton.mp second
      subst frame
      exact MeasurementCells.context_auxiliarySpace_mono _ 2 (Nat.zero_le (sampleWidth I))
  · obtain ⟨used, bounded, rfl⟩ := MeasurementCells.allocate_visitedContexts _ _ _ _ _ later
    exact MeasurementCells.context_auxiliarySpace_mono _ 2 bounded

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
