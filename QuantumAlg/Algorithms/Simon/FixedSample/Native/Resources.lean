/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Recovery
import all QuantumAlg.Components.Classical.GF2.Native.Retained.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Resources of actual fixed-sample Simon recovery

One preparation creates the sole two-register bank. The first sample uses
that preparation; each later sample pays for reset of every bank wire. Each
round measures the original first register and packs it into its retained
slot. The final GF(2) recovery runs once. Independent event envelopes include
both reset corrections, while actual counts charge the selected correction.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native

open Execution

noncomputable section

/-- Original unitary allowance together with each real Z and the paid row packing. -/
def sampleEnvelope (n : Nat) : ResourcePool .quantum :=
  circuitEventLimit n + (n • ResourcePool.singleton (Circuit.zEvent 2) +
    ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits n))))

/-- Fixed slots are sampled in order; every successor includes both reset alternatives. -/
def sampleBatchEnvelope (n count : Nat) : ResourcePool .quantum :=
  count • sampleEnvelope n + (count - 1) • ZReset.Bank.envelope (2 * n)

/-- One actual preparation precedes the independent finite sampling envelope. -/
def samplingEnvelope (n count : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (preparation n).event + sampleBatchEnvelope n count

/-- The original polynomial recovery allowance is added once after sampling. -/
def recoveryEnvelope (n count : Nat) : ResourcePool .quantum :=
  samplingEnvelope n count + ClassicalRoutines.GF2.Native.intoEnvelope .quantum count n

/-- Actual selected reset corrections contribute two events per existing bank wire. -/
def samplingEventLimit (n count : Nat) : Nat :=
  1 + count * (3 * n + 2) + (count - 1) * (4 * n)

/-- The original member critical path is at most three, followed by sequential Zs and packing. -/
def samplingDepthLimit (n count : Nat) : Nat :=
  1 + count * (n + 4) + (count - 1) * (4 * n)

/-- Real resident sampling storage: finite cells, one bank and all retained sample slots. -/
def samplingSpace (n count : Nat) : SpacePool .quantum :=
  n • SpacePool.ofShape (.finite 2) + SpacePool.ofQuantumLayout (bankLayout n) +
    count • SpacePool.ofShape (.bits n)

/-- Reset and recovery use sequential lexical allowances beside the same persistent samples. -/
def recoveryScratchSpace (n count : Nat) : SpacePool .quantum :=
  SpacePool.max (SpacePool.ofShape (.finite 2))
    (((ClassicalRoutines.GF2.Native.stateShapes count n).map SpacePool.ofShape).sum +
      ClassicalRoutines.GF2.Native.intoScratchSpace .quantum count n +
        SpacePool.ofShape (.option (.unsignedWord n)))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

private theorem context_width : (context base noQuantum n count).systemCount = 2 * n := by
  have same := congrArg List.length (nativeSimon_context_wires base noQuantum n count)
  simpa only [RuntimeCtx.systemCount, QuantumLayout.wires_length] using same

private theorem readouts_events
    (path : (Circuit.measurementSequence (readouts base noQuantum n count)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum n count)).eventTrace path =
      List.replicate n (Circuit.zEvent 2) := by
  rw [Circuit.measurementSequence_eventTrace, readouts, List.map_ofFn]
  simp only [nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count)]
  exact List.ofFn_const _ _

private theorem readouts_depth
    (path : (Circuit.measurementSequence (readouts base noQuantum n count)).Path) :
    (Circuit.measurementSequence (readouts base noQuantum n count)).depth (fun _ => 1) path =
      n := by
  rw [Circuit.measurementSequence_unitDepth, readouts, List.length_ofFn]

/-- Real measurement and paid packing follow the unchanged original unitary trace. -/
theorem nativeSimon_sample_eventTrace (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    (sample base noQuantum n count sampling index).eventTrace path =
      sampling.circuit.eventTrace ++ (List.replicate n (Circuit.zEvent 2) ++
        [.classicalOperation (.nominalEncoding (.packFiniteBits n))]) := by
  change (member n (nativeSimon_context_wires base noQuantum n count) sampling).eventTrace ++
    ((Circuit.measurementSequence (readouts base noQuantum n count)).eventTrace path.2.1 ++
      [.classicalOperation (.nominalEncoding (.packFiniteBits n))]) = _
  rw [readouts_events]
  simp only [member, UnitaryCircuit.reindex_eventTrace]

/-- The same sampled path uses exactly the independent original-member and boundary allowance. -/
theorem nativeSimon_sample_pool (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    (sample base noQuantum n count sampling index).resourcePool path = sampleEnvelope n := by
  rw [Circuit.resourcePool, nativeSimon_sample_eventTrace]
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    add_zero, UnitaryCircuit.ofList_eventTrace_eq_eventCost, sampling.circuitEventCost,
    ResourcePool.ofList_replicate, ResourcePool.scale, sampleEnvelope]

/-- The real sample count includes the original 2n Hadamards, oracle, n Zs and one pack. -/
theorem nativeSimon_sample_eventCount (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    ((sample base noQuantum n count sampling index).eventTrace path).length = 3 * n + 2 := by
  have pool := congrArg Multiset.card
    (nativeSimon_sample_pool base noQuantum n count sampling index path)
  simp only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card, sampleEnvelope,
    circuitEventLimit, Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate,
    Multiset.card_nsmul] at pool
  omega

/-- Unit depth preserves the original member's critical path and charges every terminal step. -/
theorem nativeSimon_sample_depth_le (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    (sample base noQuantum n count sampling index).depth (fun _ => 1) path ≤ n + 4 := by
  change DepthExpr.depthEval (fun _ => 1)
    (member n (nativeSimon_context_wires base noQuantum n count) sampling).eventDepth +
      ((Circuit.measurementSequence (readouts base noQuantum n count)).depth (fun _ => 1)
        path.2.1 + 1) ≤ _
  rw [readouts_depth]
  simp only [member, UnitaryCircuit.reindex_eventDepth]
  have original := sampling.circuitUnitDepth
  omega

/-- Every later sample charges the full bank reset before the same original sampling body. -/
theorem nativeSimon_reusedSample_pool_le (sampling : SamplingCircuit n) (index : Fin count)
    (path : (reusedSample base noQuantum n count sampling index).Path) :
    (reusedSample base noQuantum n count sampling index).resourcePool path ≤
      ZReset.Bank.envelope (2 * n) + sampleEnvelope n := by
  change ResourcePool.ofList ((reset base noQuantum n count).eventTrace path.1 ++
    (sample base noQuantum n count sampling index).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  have bound := ZReset.BankScope.zResetBankScope_resourcePool_le
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count)) path.1
  rw [context_width] at bound
  exact add_le_add bound (nativeSimon_sample_pool base noQuantum n count sampling index path.2).le

/-- Actual reset uses one selected correction, so each successor adds exactly 4n events. -/
theorem nativeSimon_reusedSample_eventCount (sampling : SamplingCircuit n) (index : Fin count)
    (path : (reusedSample base noQuantum n count sampling index).Path) :
    ((reusedSample base noQuantum n count sampling index).eventTrace path).length =
      4 * n + (3 * n + 2) := by
  change ((reset base noQuantum n count).eventTrace path.1 ++
    (sample base noQuantum n count sampling index).eventTrace path.2).length = _
  rw [List.length_append, nativeSimon_sample_eventCount]
  have actual := ZReset.BankScope.zResetBankScope_eventTrace_length
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count)) path.1
  rw [context_width] at actual
  change ((reset base noQuantum n count).eventTrace path.1).length = 2 * (2 * n) at actual
  rw [actual]
  omega

/-- Sequential reset depth is charged before the original three-layer sampling contract. -/
theorem nativeSimon_reusedSample_depth_le (sampling : SamplingCircuit n) (index : Fin count)
    (path : (reusedSample base noQuantum n count sampling index).Path) :
    (reusedSample base noQuantum n count sampling index).depth (fun _ => 1) path ≤
      4 * n + (n + 4) := by
  change (reset base noQuantum n count).depth (fun _ => 1) path.1 +
    (sample base noQuantum n count sampling index).depth (fun _ => 1) path.2 ≤ _
  have actual := ZReset.BankScope.zResetBankScope_unitDepth
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count)) path.1
  rw [context_width] at actual
  have sampled := nativeSimon_sample_depth_le base noQuantum n count sampling index path.2
  change (reset base noQuantum n count).depth (fun _ => 1) path.1 = 2 * (2 * n) at actual
  omega

/-- The literal finite loop stays below the original member and reset coordinate envelope. -/
theorem nativeSimon_sampleBatch_pool_le (sampling : SamplingCircuit n)
    (path : (sampleBatch base noQuantum n sampling count).Path) :
    (sampleBatch base noQuantum n sampling count).resourcePool path ≤
      sampleBatchEnvelope n count := by
  cases count with
  | zero => simp [sampleBatch, Circuit.resourcePool, Circuit.eventTrace, sampleBatchEnvelope]
  | succ count =>
      change ResourcePool.ofList
        ((sample base noQuantum n (count + 1) sampling 0).eventTrace path.1 ++
          (Circuit.forRange count (fun index =>
            reusedSample base noQuantum n (count + 1) sampling index.succ)).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append]
      have later := Circuit.forRange_pool_le count
        (fun index => reusedSample base noQuantum n (count + 1) sampling index.succ)
        (ZReset.Bank.envelope (2 * n) + sampleEnvelope n)
        (fun index record => nativeSimon_reusedSample_pool_le base noQuantum n (count + 1)
          sampling index.succ record) path.2
      refine (add_le_add
        (nativeSimon_sample_pool base noQuantum n (count + 1) sampling 0 path.1).le
        later).trans_eq ?_
      simp only [sampleBatchEnvelope, Nat.add_sub_cancel, ResourcePool.scale,
        succ_nsmul, nsmul_add]
      ac_rfl

/-- The actual fixed loop counts only selected reset corrections at each successor. -/
theorem nativeSimon_sampleBatch_eventCount_le (sampling : SamplingCircuit n)
    (path : (sampleBatch base noQuantum n sampling count).Path) :
    ((sampleBatch base noQuantum n sampling count).eventTrace path).length ≤
      count * (3 * n + 2) + (count - 1) * (4 * n) := by
  cases count with
  | zero => simp [sampleBatch, Circuit.eventTrace]
  | succ count =>
      change ((sample base noQuantum n (count + 1) sampling 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index =>
          reusedSample base noQuantum n (count + 1) sampling index.succ)).eventTrace
          path.2).length ≤ _
      rw [List.length_append, nativeSimon_sample_eventCount]
      have later := Circuit.forRange_eventCount_le count
        (fun index => reusedSample base noQuantum n (count + 1) sampling index.succ)
        (4 * n + (3 * n + 2))
        (fun index record => (nativeSimon_reusedSample_eventCount base noQuantum n (count + 1)
          sampling index.succ record).le) path.2
      simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_add] at *
      omega

/-- The original unitary critical path is retained in the real sequential finite loop. -/
theorem nativeSimon_sampleBatch_depth_le (sampling : SamplingCircuit n)
    (path : (sampleBatch base noQuantum n sampling count).Path) :
    (sampleBatch base noQuantum n sampling count).depth (fun _ => 1) path ≤
      count * (n + 4) + (count - 1) * (4 * n) := by
  cases count with
  | zero => simp [sampleBatch, Circuit.depth, Circuit.eventDepth]
  | succ count =>
      change (sample base noQuantum n (count + 1) sampling 0).depth (fun _ => 1) path.1 +
        (Circuit.forRange count (fun index =>
          reusedSample base noQuantum n (count + 1) sampling index.succ)).depth
            (fun _ => 1) path.2 ≤ _
      have first := nativeSimon_sample_depth_le base noQuantum n (count + 1) sampling 0 path.1
      have later := Circuit.forRange_depth_le count
        (fun index => reusedSample base noQuantum n (count + 1) sampling index.succ)
        (4 * n + (n + 4))
        (fun index record => nativeSimon_reusedSample_depth_le base noQuantum n (count + 1)
          sampling index.succ record) path.2
      simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_add] at *
      omega

private theorem allocateSlots_events (path : (allocateSlots base n count).Path) :
    (allocateSlots base n count).eventTrace path = [] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocateSlots base n count).eventTrace path.1 ++ [] = []
      rw [ih]
      rfl

private theorem allocateSlots_depth (path : (allocateSlots base n count).Path) :
    (allocateSlots base n count).depth (fun _ => 1) path = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (allocateSlots base n count).depth (fun _ => 1) path.1 + 0 = 0
      rw [ih]

/-- Real initialization emits exactly one basis-preparation event. -/
theorem nativeSimon_allocate_events (path : (allocate base noQuantum n count).Path) :
    (allocate base noQuantum n count).eventTrace path = [(preparation n).event] := by
  change (allocateSlots base n count).eventTrace path.1 ++
    ([(preparation n).event] ++
      (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n).eventTrace path.2.2) = _
  rw [allocateSlots_events]
  erw [MeasurementCells.allocate_eventTrace]
  rfl

/-- Retaining the real classical banks adds no native-event depth to the one preparation. -/
theorem nativeSimon_allocate_depth (path : (allocate base noQuantum n count).Path) :
    (allocate base noQuantum n count).depth (fun _ => 1) path = 1 := by
  change (allocateSlots base n count).depth (fun _ => 1) path.1 +
    (1 + (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n).depth
      (fun _ => 1) path.2.2) = _
  rw [allocateSlots_depth]
  erw [MeasurementCells.allocate_depth]

/-- The complete actual sampler fits the independent coordinate allowance. -/
theorem nativeSimon_code_pool_le (sampling : SamplingCircuit n)
    (path : (code base noQuantum n count sampling).Path) :
    (code base noQuantum n count sampling).resourcePool path ≤ samplingEnvelope n count := by
  change ResourcePool.ofList ((allocate base noQuantum n count).eventTrace path.1 ++
    (sampleBatch base noQuantum n sampling count).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, nativeSimon_allocate_events]
  exact add_le_add le_rfl (nativeSimon_sampleBatch_pool_le base noQuantum n count sampling path.2)

/-- Same-path native count includes one initialization and the actual successor resets. -/
theorem nativeSimon_code_eventCount_le (sampling : SamplingCircuit n)
    (path : (code base noQuantum n count sampling).Path) :
    ((code base noQuantum n count sampling).eventTrace path).length ≤
      samplingEventLimit n count := by
  change ((allocate base noQuantum n count).eventTrace path.1 ++
    (sampleBatch base noQuantum n sampling count).eventTrace path.2).length ≤ _
  rw [List.length_append, nativeSimon_allocate_events]
  have bound := nativeSimon_sampleBatch_eventCount_le base noQuantum n count sampling path.2
  simp only [samplingEventLimit, List.length_singleton]
  omega

/-- Same-path depth uses the original member layers and all actual sequential boundaries. -/
theorem nativeSimon_code_depth_le (sampling : SamplingCircuit n)
    (path : (code base noQuantum n count sampling).Path) :
    (code base noQuantum n count sampling).depth (fun _ => 1) path ≤
      samplingDepthLimit n count := by
  change (allocate base noQuantum n count).depth (fun _ => 1) path.1 +
    (sampleBatch base noQuantum n sampling count).depth (fun _ => 1) path.2 ≤ _
  rw [nativeSimon_allocate_depth]
  have bound := nativeSimon_sampleBatch_depth_le base noQuantum n count sampling path.2
  unfold samplingDepthLimit
  omega

/-- The real sampling-and-recovery program fits the independent complete event envelope. -/
theorem nativeSimon_recovery_pool_le (sampling : SamplingCircuit n)
    (path : (recoveryCode base noQuantum n count sampling).Path) :
    (recoveryCode base noQuantum n count sampling).resourcePool path ≤
      recoveryEnvelope n count := by
  change ResourcePool.ofList ((code base noQuantum n count sampling).eventTrace path.1 ++
    (ClassicalRoutines.GF2.Native.retainedCircuit (samplesInput base noQuantum n count)
      (context base noQuantum n count).canonicalFreshKey
      (context base noQuantum n count).canonicalFreshKey_fresh).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (nativeSimon_code_pool_le base noQuantum n count sampling path.1)
    (ClassicalRoutines.GF2.Native.gf2Retained_pool_le _ _ _ path.2)

/-- Original polynomial recovery contributes its complete serial instruction ceiling once. -/
theorem nativeSimon_recovery_eventCount_le (sampling : SamplingCircuit n)
    (path : (recoveryCode base noQuantum n count sampling).Path) :
    ((recoveryCode base noQuantum n count sampling).eventTrace path).length ≤
      samplingEventLimit n count +
        ClassicalRoutines.GF2.Native.intoDepthLimit (kind := .quantum) count n (fun _ => 1) := by
  change ((code base noQuantum n count sampling).eventTrace path.1 ++
    (ClassicalRoutines.GF2.Native.retainedCircuit (samplesInput base noQuantum n count)
      (context base noQuantum n count).canonicalFreshKey
      (context base noQuantum n count).canonicalFreshKey_fresh).eventTrace path.2).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add (nativeSimon_code_eventCount_le base noQuantum n count sampling path.1)
    (ClassicalRoutines.GF2.Native.gf2Retained_eventCount_le _ _ _ path.2)

/-- The actual final recovery depth is added after the original quantum member critical paths. -/
theorem nativeSimon_recovery_depth_le (sampling : SamplingCircuit n)
    (path : (recoveryCode base noQuantum n count sampling).Path) :
    (recoveryCode base noQuantum n count sampling).depth (fun _ => 1) path ≤
      samplingDepthLimit n count +
        ClassicalRoutines.GF2.Native.intoDepthLimit (kind := .quantum) count n (fun _ => 1) := by
  change (code base noQuantum n count sampling).depth (fun _ => 1) path.1 +
    (ClassicalRoutines.GF2.Native.retainedCircuit (samplesInput base noQuantum n count)
      (context base noQuantum n count).canonicalFreshKey
      (context base noQuantum n count).canonicalFreshKey_fresh).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add (nativeSimon_code_depth_le base noQuantum n count sampling path.1)
    (ClassicalRoutines.GF2.Native.gf2Retained_depth_le _ _ _ _ path.2)

private theorem slots_resident : (slots base n count).residentSpace =
    count • SpacePool.ofShape (.bits n) + base.residentSpace := by
  induction count with
  | zero => simp [slots]
  | succ count ih =>
      rw [slots, RuntimeCtx.residentSpace_addRetained, ih, succ_nsmul]
      ac_rfl

private theorem slots_auxiliary : (slots base n count).auxiliarySpace =
    count • SpacePool.ofShape (.bits n) + base.auxiliarySpace := by
  induction count with
  | zero => simp [slots]
  | succ count ih =>
      rw [slots, RuntimeCtx.auxiliarySpace_addRetained, ih, succ_nsmul]
      ac_rfl

/-- All live sampling cells and the single original bank retain the complete caller footprint. -/
theorem nativeSimon_context_residentSpace : (context base noQuantum n count).residentSpace =
    samplingSpace n count + base.residentSpace := by
  simp only [context, MeasurementCells.context_residentSpace, bankContext,
    RuntimeCtx.residentSpace_addOwnedLayout, slots_resident, samplingSpace, add_assoc]

/-- Every new sampling entry is auxiliary, beside the caller's own auxiliary roles. -/
theorem nativeSimon_context_auxiliarySpace : (context base noQuantum n count).auxiliarySpace =
    samplingSpace n count + base.auxiliarySpace := by
  simp only [context, MeasurementCells.context_auxiliarySpace, bankContext,
    RuntimeCtx.auxiliarySpace_addOwnedLayout, slots_auxiliary, samplingSpace, add_assoc]

private theorem slots_visited (path : (allocateSlots base n count).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈ (allocateSlots base n count).visitedContexts path) :
    ∃ used, used ≤ count ∧ frame = slots base n used := by
  induction count with
  | zero => exact ⟨0, le_rfl, List.mem_singleton.mp present⟩
  | succ count ih =>
      change frame ∈ (allocateSlots base n count).visitedContexts path.1 ++
        [slots base n count, slots base n (count + 1)] at present
      rcases List.mem_append.mp present with earlier | later
      · obtain ⟨used, bound, same⟩ := ih path.1 earlier
        exact ⟨used, Nat.le_succ_of_le bound, same⟩
      · rcases List.mem_cons.mp later with same | last
        · exact ⟨count, Nat.le_succ count, same⟩
        · exact ⟨count + 1, le_rfl, List.mem_singleton.mp last⟩

private theorem allocate_visited (path : (allocate base noQuantum n count).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈ (allocate base noQuantum n count).visitedContexts path) :
    (∃ used, used ≤ count ∧ frame = slots base n used) ∨
      ∃ used, used ≤
      n ∧ frame = MeasurementCells.context (bankContext base noQuantum n count) 2 used := by
  change frame ∈ (allocateSlots base n count).visitedContexts path.1 ++
    ([slots base n count, bankContext base noQuantum n count] ++
      (MeasurementCells.allocate (bankContext base noQuantum n count) 2 n).visitedContexts
        path.2.2) at present
  rcases List.mem_append.mp present with earlier | later
  · exact Or.inl (slots_visited base n count path.1 frame earlier)
  · rcases List.mem_append.mp later with boundary | cells
    · rcases List.mem_cons.mp boundary with first | second
      · exact Or.inl ⟨count, le_rfl, first⟩
      · exact Or.inr ⟨0, Nat.zero_le n, List.mem_singleton.mp second⟩
    · exact Or.inr (MeasurementCells.allocate_visitedContexts _ _ _ _ _ cells)

private theorem allocate_resident (path : (allocate base noQuantum n count).Path) :
    (allocate base noQuantum n count).peakResidentSpace path ≤
      (context base noQuantum n count).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  rcases allocate_visited base noQuantum n count path frame present with earlier | cells
  · obtain ⟨used, bounded, rfl⟩ := earlier
    rw [slots_resident, nativeSimon_context_residentSpace, samplingSpace]
    intro axis
    have mul := Nat.mul_le_mul_right (SpacePool.ofShape (.bits n) axis) bounded
    change used * SpacePool.ofShape (.bits n) axis + base.residentSpace axis ≤
      n * SpacePool.ofShape (.finite 2) axis + SpacePool.ofQuantumLayout (bankLayout n) axis +
        count * SpacePool.ofShape (.bits n) axis + base.residentSpace axis
    omega
  · obtain ⟨used, bounded, rfl⟩ := cells
    exact MeasurementCells.context_residentSpace_mono _ 2 bounded

private theorem allocate_auxiliary (path : (allocate base noQuantum n count).Path) :
    (allocate base noQuantum n count).peakAuxiliarySpace path ≤
      (context base noQuantum n count).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  rcases allocate_visited base noQuantum n count path frame present with earlier | cells
  · obtain ⟨used, bounded, rfl⟩ := earlier
    rw [slots_auxiliary, nativeSimon_context_auxiliarySpace, samplingSpace]
    intro axis
    have mul := Nat.mul_le_mul_right (SpacePool.ofShape (.bits n) axis) bounded
    change used * SpacePool.ofShape (.bits n) axis + base.auxiliarySpace axis ≤
      n * SpacePool.ofShape (.finite 2) axis + SpacePool.ofQuantumLayout (bankLayout n) axis +
        count * SpacePool.ofShape (.bits n) axis + base.auxiliarySpace axis
    omega
  · obtain ⟨used, bounded, rfl⟩ := cells
    exact MeasurementCells.context_auxiliarySpace_mono _ 2 bounded

private theorem sample_visited (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) (frame : RuntimeCtx .quantum)
    (present : frame ∈ (sample base noQuantum n count sampling index).visitedContexts path) :
    frame = context base noQuantum n count := by
  change frame ∈ [context base noQuantum n count] ++
    ((Circuit.measurementSequence (readouts base noQuantum n count)).visitedContexts path.2.1 ++
      [context base noQuantum n count]) at present
  rw [Circuit.measurementSequence_visitedContexts] at present
  simp only [List.mem_append, List.mem_singleton, List.mem_replicate] at present
  rcases present with same | ⟨_, same⟩ | same <;> exact same

private theorem sample_resident (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    (sample base noQuantum n count sampling index).peakResidentSpace path ≤
      (context base noQuantum n count).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro frame present
  rw [sample_visited base noQuantum n count sampling index path frame present]

private theorem sample_auxiliary (sampling : SamplingCircuit n) (index : Fin count)
    (path : (sample base noQuantum n count sampling index).Path) :
    (sample base noQuantum n count sampling index).peakAuxiliarySpace path ≤
      (context base noQuantum n count).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro frame present
  rw [sample_visited base noQuantum n count sampling index path frame present]

private theorem reusedSample_resident (sampling : SamplingCircuit n) (index : Fin count)
    (path : (reusedSample base noQuantum n count sampling index).Path) :
    (reusedSample base noQuantum n count sampling index).peakResidentSpace path ≤
      SpacePool.ofShape (.finite 2) + (context base noQuantum n count).residentSpace := by
  refine (Circuit.peakResidentSpace_seq (reset base noQuantum n count)
    (sample base noQuantum n count sampling index) path).le.trans ?_
  apply SpacePool.max_le
  · exact (ZReset.BankScope.zResetBankScope_peakResidentSpace _ path.1).le
  · refine (sample_resident base noQuantum n count sampling index path.2).trans ?_
    intro axis
    exact Nat.le_add_left _ _

private theorem reusedSample_auxiliary (sampling : SamplingCircuit n) (index : Fin count)
    (path : (reusedSample base noQuantum n count sampling index).Path) :
    (reusedSample base noQuantum n count sampling index).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.finite 2) + (context base noQuantum n count).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (reset base noQuantum n count)
    (sample base noQuantum n count sampling index) path).le.trans ?_
  apply SpacePool.max_le
  · exact (ZReset.BankScope.zResetBankScope_peakAuxiliarySpace _ path.1).le
  · refine (sample_auxiliary base noQuantum n count sampling index path.2).trans ?_
    intro axis
    exact Nat.le_add_left _ _

private theorem sampleBatch_resident (sampling : SamplingCircuit n)
    (path : (sampleBatch base noQuantum n sampling count).Path) :
    (sampleBatch base noQuantum n sampling count).peakResidentSpace path ≤
      SpacePool.ofShape (.finite 2) + (context base noQuantum n count).residentSpace := by
  cases count with
  | zero =>
      apply Circuit.peakResidentSpace_le_of_visited
      intro frame present
      have same := List.mem_singleton.mp present
      subst frame
      intro axis
      exact Nat.le_add_left _ _
  | succ count =>
      refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (sample_resident base noQuantum n (count + 1) sampling 0 path.1).trans ?_
        intro axis
        exact Nat.le_add_left _ _
      · exact Circuit.forRange_resident_le count _ _ (fun _ => Nat.le_add_left _ _)
          (fun index record => reusedSample_resident base noQuantum n (count + 1)
            sampling index.succ record) path.2

private theorem sampleBatch_auxiliary (sampling : SamplingCircuit n)
    (path : (sampleBatch base noQuantum n sampling count).Path) :
    (sampleBatch base noQuantum n sampling count).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.finite 2) + (context base noQuantum n count).auxiliarySpace := by
  cases count with
  | zero =>
      apply Circuit.peakAuxiliarySpace_le_of_visited
      intro frame present
      have same := List.mem_singleton.mp present
      subst frame
      intro axis
      exact Nat.le_add_left _ _
  | succ count =>
      refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
      · refine (sample_auxiliary base noQuantum n (count + 1) sampling 0 path.1).trans ?_
        intro axis
        exact Nat.le_add_left _ _
      · exact Circuit.forRange_auxiliary_le count _ _ (fun _ => Nat.le_add_left _ _)
          (fun index record => reusedSample_auxiliary base noQuantum n (count + 1)
            sampling index.succ record) path.2

/-- All sampled storage remains live, with one reset scratch reused across successors. -/
theorem nativeSimon_code_resident_le (sampling : SamplingCircuit n)
    (path : (code base noQuantum n count sampling).Path) :
    (code base noQuantum n count sampling).peakResidentSpace path ≤
      SpacePool.ofShape (.finite 2) + samplingSpace n count + base.residentSpace := by
  rw [add_assoc, ← nativeSimon_context_residentSpace base noQuantum n count]
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (allocate_resident base noQuantum n count path.1).trans ?_
    intro axis
    exact Nat.le_add_left _ _
  · exact sampleBatch_resident base noQuantum n count sampling path.2

/-- The same live sampling entries are charged in auxiliary storage according to their roles. -/
theorem nativeSimon_code_auxiliary_le (sampling : SamplingCircuit n)
    (path : (code base noQuantum n count sampling).Path) :
    (code base noQuantum n count sampling).peakAuxiliarySpace path ≤
      SpacePool.ofShape (.finite 2) + samplingSpace n count + base.auxiliarySpace := by
  rw [add_assoc, ← nativeSimon_context_auxiliarySpace base noQuantum n count]
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (allocate_auxiliary base noQuantum n count path.1).trans ?_
    intro axis
    exact Nat.le_add_left _ _
  · exact sampleBatch_auxiliary base noQuantum n count sampling path.2

/-- Recovery uses one seven-cell workspace after sampling, retaining the complete original bank. -/
theorem nativeSimon_recovery_resident_le (sampling : SamplingCircuit n)
    (path : (recoveryCode base noQuantum n count sampling).Path) :
    (recoveryCode base noQuantum n count sampling).peakResidentSpace path ≤
      recoveryScratchSpace n count + samplingSpace n count + base.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (nativeSimon_code_resident_le base noQuantum n count sampling path.1).trans ?_
    exact add_le_add (add_le_add (SpacePool.le_max_left _ _) le_rfl) le_rfl
  · have bound := ClassicalRoutines.GF2.Native.gf2Retained_resident_le
      (samplesInput base noQuantum n count) (context base noQuantum n count).canonicalFreshKey
      (context base noQuantum n count).canonicalFreshKey_fresh path.2
    rw [nativeSimon_context_residentSpace] at bound
    refine bound.trans ?_
    intro axis
    have maxBound := SpacePool.le_max_right
      (SpacePool.ofShape (.finite 2))
      (((ClassicalRoutines.GF2.Native.stateShapes count n).map SpacePool.ofShape).sum +
        ClassicalRoutines.GF2.Native.intoScratchSpace .quantum count n +
          SpacePool.ofShape (.option (.unsignedWord n))) axis
    simpa only [recoveryScratchSpace, Pi.add_apply, Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_right maxBound (samplingSpace n count axis))
        (base.residentSpace axis)

/-- Auxiliary storage is the same owned allowance beside the caller's existing auxiliary cells. -/
theorem nativeSimon_recovery_auxiliary_le (sampling : SamplingCircuit n)
    (path : (recoveryCode base noQuantum n count sampling).Path) :
    (recoveryCode base noQuantum n count sampling).peakAuxiliarySpace path ≤
      recoveryScratchSpace n count + samplingSpace n count + base.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (nativeSimon_code_auxiliary_le base noQuantum n count sampling path.1).trans ?_
    exact add_le_add (add_le_add (SpacePool.le_max_left _ _) le_rfl) le_rfl
  · have bound := ClassicalRoutines.GF2.Native.gf2Retained_auxiliary_le
      (samplesInput base noQuantum n count) (context base noQuantum n count).canonicalFreshKey
      (context base noQuantum n count).canonicalFreshKey_fresh path.2
    rw [nativeSimon_context_auxiliarySpace] at bound
    refine bound.trans ?_
    intro axis
    have maxBound := SpacePool.le_max_right
      (SpacePool.ofShape (.finite 2))
      (((ClassicalRoutines.GF2.Native.stateShapes count n).map SpacePool.ofShape).sum +
        ClassicalRoutines.GF2.Native.intoScratchSpace .quantum count n +
          SpacePool.ofShape (.option (.unsignedWord n))) axis
    simpa only [recoveryScratchSpace, Pi.add_apply, Nat.add_assoc] using
      Nat.add_le_add_right (Nat.add_le_add_right maxBound (samplingSpace n count axis))
        (base.auxiliarySpace axis)

end

end QuantumAlg.SimonsProblem.FixedSample.Native
