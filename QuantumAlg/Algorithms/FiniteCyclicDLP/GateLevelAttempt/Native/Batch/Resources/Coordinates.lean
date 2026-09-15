/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.GateLevelAttempt.Native.Batch.Resources

/-!
# Exact coordinates of the actual retained finite-cyclic sample batch

Every real sample invokes one original encoded query and both original inverse
Fourier circuits. Only later samples pay the complete-bank reset. Its two
cyclic shifts per wire, including zero shifts, and its measurement are counted
separately from the original member. All result cells and the original bank
remain present in the complete returned state.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch

open Execution

noncomputable section

universe u

variable {G : Type u} [Group G]

private theorem range_observation {ctx : RuntimeCtx .quantum}
    (observe : ResourcePool .quantum → Nat) (empty : observe 0 = 0)
    (additive : ∀ left right, observe (left + right) = observe left + observe right)
    (amount count : Nat) (body : Fin count → Circuit ctx ctx)
    (same : ∀ index path, observe ((body index).resourcePool path) = amount)
    (path : (Circuit.forRange count body).Path) :
    observe ((Circuit.forRange count body).resourcePool path) = count * amount := by
  induction count with
  | zero =>
      simpa only [Circuit.forRange, Circuit.resourcePool, Circuit.eventTrace,
        ResourcePool.ofList_nil, Nat.zero_mul] using empty
  | succ count ih =>
      change observe (ResourcePool.ofList ((body 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2)) = _
      rw [ResourcePool.ofList_append, additive]
      erw [same, ih _ (fun index => same index.succ)]
      simp [Nat.succ_mul, Nat.add_comm]

private theorem run_observation
    (observe : ResourcePool .quantum → Nat) (empty : observe 0 = 0)
    (additive : ∀ left right, observe (left + right) = observe left + observe right)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (offPrepared : observe (ResourcePool.singleton (Native.preparation P ux).event) = 0)
    (sampleAmount resetAmount : Nat)
    (sampleSame : ∀ slot path,
      observe ((sample base noQuantum P count B ux slot).resourcePool path) = sampleAmount)
    (resetSame : ∀ slot path,
      observe ((reset base noQuantum P count ux slot).resourcePool path) = resetAmount)
    (path : (run base noQuantum P count B ux).code.Path) :
    observe ((run base noQuantum P count B ux).code.resourcePool path) =
      count * sampleAmount + (count - 1) * resetAmount := by
  change observe (ResourcePool.ofList ((allocate base noQuantum P count ux).eventTrace path.1 ++
    (sampleBatch base noQuantum P B ux count).eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, additive, nativeFiniteCyclicBatch_allocate_events]
  change observe (ResourcePool.singleton (Native.preparation P ux).event) + _ = _
  rw [offPrepared, zero_add]
  cases count with
  | zero =>
      simpa only [sampleBatch, Circuit.eventTrace, ResourcePool.ofList_nil,
        Nat.zero_mul, Nat.zero_sub, Nat.add_zero] using empty
  | succ count =>
      change observe (ResourcePool.ofList
        ((sample base noQuantum P (count + 1) B ux 0).eventTrace path.2.1 ++
          (Circuit.forRange count (fun index =>
            reusedSample base noQuantum P (count + 1) B ux index.succ)).eventTrace path.2.2)) = _
      rw [ResourcePool.ofList_append, additive]
      erw [sampleSame]
      have later := range_observation observe empty additive (resetAmount + sampleAmount) count
        (fun index => reusedSample base noQuantum P (count + 1) B ux index.succ)
        (fun index iteration => by
          change observe (ResourcePool.ofList
            ((reset base noQuantum P (count + 1) ux index.succ).eventTrace iteration.1 ++
              (sample base noQuantum P (count + 1) B ux index.succ).eventTrace iteration.2)) = _
          rw [ResourcePool.ofList_append, additive]
          exact congrArg₂ (· + ·) (resetSame index.succ iteration.1)
            (sampleSame index.succ iteration.2)) path.2.2
      change sampleAmount + observe ((Circuit.forRange count (fun index =>
        reusedSample base noQuantum P (count + 1) B ux index.succ)).resourcePool path.2.2) = _
      rw [later]
      simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_add]
      omega

private theorem reset_coordinate
    (event : Resource.Event .quantum)
    (measured : ∀ dimension : ℕ+, event ≠ Circuit.zEvent dimension)
    (shifted : ∀ (dimension : ℕ+) (amount : Fin dimension),
      event ≠ .gate (QuditShift.gateLabel amount))
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat) (ux : UxAccess P) (slot : Fin count)
    (path : (reset base noQuantum P count ux slot).Path) :
    ResourcePool.count event ((reset base noQuantum P count ux slot).resourcePool path) = 0 := by
  have stage : ∀ (dimension : ℕ+) (value : Fin dimension),
      ResourcePool.count event (resetStageEnvelope dimension value) = 0 := by
    intro dimension value
    simp [resetStageEnvelope, ResourcePool.ofList, ResourcePool.count,
      ResourcePool.singleton, measured, shifted, eq_comm]
  have absent : ResourcePool.count event (resetEnvelope P ux) = 0 := by
    unfold resetEnvelope
    induction (Finset.univ : Finset (Fin (totalQubits P))) using Finset.induction_on with
    | empty => simp
    | @insert index rest fresh ih =>
        erw [Finset.sum_insert fresh, ResourcePool.count_add, stage, ih, zero_add]
  have bounded := (ResourcePool.le_iff_count.mp
    (nativeFiniteCyclicBatch_reset_pool_le base noQuantum P count slot ux path)) event
  rw [absent] at bounded
  exact Nat.eq_zero_of_le_zero bounded

private theorem sample_coordinate (event : Resource.Event .quantum)
    (measured : event ≠ Circuit.zEvent 2)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) (slot : Fin count)
    (path : (sample base noQuantum P count B ux slot).Path) :
    ResourcePool.count event ((sample base noQuantum P count B ux slot).resourcePool path) =
      ResourcePool.count event (GateLevelAttempt.quantumCircuit P B ux).eventCost := by
  rw [nativeFiniteCyclicBatch_sample_pool]
  unfold sampleEnvelope unitaryEnvelope
  rw [← inverseQFTCircuit_eventCost_eq_pair, ← GateLevelAttempt.quantumCircuit_eventCost P B ux]
  simp [ResourcePool.count_add, ResourcePool.count_singleton_of_ne measured]

private theorem run_coordinate (event : Resource.Event .quantum)
    (measured : ∀ dimension : ℕ+, event ≠ Circuit.zEvent dimension)
    (shifted : ∀ (dimension : ℕ+) (amount : Fin dimension),
      event ≠ .gate (QuditShift.gateLabel amount))
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (prepared : event ≠ (Native.preparation P ux).event)
    (path : (run base noQuantum P count B ux).code.Path) :
    ResourcePool.count event ((run base noQuantum P count B ux).code.resourcePool path) =
      count * ResourcePool.count event (GateLevelAttempt.quantumCircuit P B ux).eventCost := by
  have counted := run_observation (ResourcePool.count event) (by simp)
    (ResourcePool.count_add event) base noQuantum P count B ux
    (ResourcePool.count_singleton_of_ne prepared 1) _ 0
    (sample_coordinate event (measured 2) base noQuantum P count B ux)
    (reset_coordinate event measured shifted base noQuantum P count ux) path
  simpa only [Nat.mul_zero, Nat.add_zero] using counted

private theorem gate_coordinate (label : Resource.GateLabel)
    (different : label.name ≠ "qudit-cyclic-shift")
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (path : (run base noQuantum P count B ux).code.Path) :
    ResourcePool.count (.gate label) ((run base noQuantum P count B ux).code.resourcePool path) =
      count * ResourcePool.count (.gate label)
        (GateLevelAttempt.quantumCircuit P B ux).eventCost :=
  run_coordinate (.gate label) (by intro dimension; simp [Circuit.zEvent])
    (fun dimension amount equality => different
      (congrArg Resource.GateLabel.name (Resource.Event.gate.inj equality)))
    base noQuantum P count B ux (by intro equality; cases equality) path

private def tally (test : Resource.Event .quantum → Bool) (pool : ResourcePool .quantum) : Nat :=
  Multiset.countP (fun event => test event) pool

private theorem tally_add (test : Resource.Event .quantum → Bool)
    (left right : ResourcePool .quantum) :
    tally test (left + right) = tally test left + tally test right := by simp [tally]

private theorem tally_nsmul (test : Resource.Event .quantum → Bool)
    (count : Nat) (pool : ResourcePool .quantum) :
    tally test (count • pool) = count * tally test pool := by
  simp [tally]

private theorem tally_list (test : Resource.Event .quantum → Bool)
    (events : List (Resource.Event .quantum)) :
    tally test (ResourcePool.ofList events) = events.countP test := by
  change events.countP (fun event => decide (test event = true)) = events.countP test
  congr 1
  funext event
  cases test event <;> rfl

private theorem tally_singleton (test : Resource.Event .quantum → Bool)
    (event : Resource.Event .quantum) (count : Nat) :
    tally test (ResourcePool.singleton event count) = count * (if test event then 1 else 0) := by
  change tally test (ResourcePool.ofList (List.replicate count event)) = _
  rw [tally_list]
  simp [List.countP_replicate]

private def isResetShift : Resource.Event .quantum → Bool
  | .gate label => label.name == "qudit-cyclic-shift"
  | _ => false

private def isMeasurement : Resource.Event .quantum → Bool
  | .measurement _ => true
  | _ => false

/-- Literal paid one-wire cyclic shifts, including both zero and nonzero amounts. -/
def resetShiftCount (pool : ResourcePool .quantum) : Nat := tally isResetShift pool

/-- Literal measurement events on the actual execution path. -/
def measurementCount (pool : ResourcePool .quantum) : Nat := tally isMeasurement pool

private theorem member_tally_zero (test : Resource.Event .quantum → Bool)
    (offElementary : ∀ event, UniformSuperposition.elementaryEvent event → test event = false)
    (offPhase : test (.gate qftControlledPhaseLabel) = false)
    (offSwap : test (.gate (.builtin "swap")) = false)
    (P : KnownOrderProblem G) (offQuery : test (uxEvent P) = false)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P) :
    tally test (GateLevelAttempt.quantumCircuit P B ux).eventCost = 0 := by
  have prepZero : tally test B.algorithm1Circuit.eventCost = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro event member observed
    have notElementary : ¬ UniformSuperposition.elementaryEvent event := by
      intro elementary
      rw [offElementary event elementary] at observed
      cases observed
    exact (Multiset.count_eq_zero.mp
      (algorithm1Circuit_count_zero_of_not_elementary B event notElementary)) member
  have hadamard : test (.gate (.builtin "hadamard")) = false :=
    offElementary _ (by simp [UniformSuperposition.elementaryEvent])
  rw [GateLevelAttempt.quantumCircuit_eventCost,
    inverseQFTCircuit_eventCost_eq_pair]
  simp only [tally_add, prepZero]
  simp [QFTCircuit_eventCost_eq, tally_add, tally_nsmul, tally_singleton,
    offQuery, hadamard, offPhase, offSwap]

private theorem shift_off_elementary (event : Resource.Event .quantum)
    (elementary : UniformSuperposition.elementaryEvent event) : isResetShift event = false := by
  simp only [UniformSuperposition.elementaryEvent, UniformSuperposition.hadamardEvent_eq_gate,
    UniformSuperposition.xEvent_eq_gate, UniformSuperposition.rotationYEvent_eq_gate,
    UniformSuperposition.cnotEvent_eq_gate] at elementary
  rcases elementary with rfl | rfl | rfl | rfl <;> rfl

private theorem measurement_off_elementary (event : Resource.Event .quantum)
    (elementary : UniformSuperposition.elementaryEvent event) : isMeasurement event = false := by
  simp only [UniformSuperposition.elementaryEvent, UniformSuperposition.hadamardEvent_eq_gate,
    UniformSuperposition.xEvent_eq_gate, UniformSuperposition.rotationYEvent_eq_gate,
    UniformSuperposition.cnotEvent_eq_gate] at elementary
  rcases elementary with rfl | rfl | rfl | rfl <;> rfl

private theorem sample_tally (test : Resource.Event .quantum → Bool)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (P : KnownOrderProblem G)
      (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)
    (slot : Fin count)
    (offMember : tally test (GateLevelAttempt.quantumCircuit P B ux).eventCost = 0)
    (path : (sample base noQuantum P count B ux slot).Path) :
    tally test ((sample base noQuantum P count B ux slot).resourcePool path) =
      sampleWidth P * (if test (Circuit.zEvent 2) then 1 else 0) := by
  rw [Circuit.resourcePool, nativeFiniteCyclicBatch_sample_eventTrace, ResourcePool.ofList_append,
    tally_add, UnitaryCircuit.ofList_eventTrace_eq_eventCost, offMember, zero_add]
  simp [tally_list, List.countP_replicate]

private theorem reset_shifts (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat) (ux : UxAccess P) (slot : Fin count)
    (path : (reset base noQuantum P count ux slot).Path) :
    tally isResetShift ((reset base noQuantum P count ux slot).resourcePool path) =
      2 * totalQubits P := by
  have counted := range_observation (tally isResetShift) (by simp [tally]) (tally_add
    isResetShift) 2 (context base noQuantum P count).systemCount
    (fun wire => QuditShift.resetWireToBasis wire (resetCell base noQuantum P count slot wire)
      (resetLabel base noQuantum P count ux wire))
    (fun wire iteration => by
      rw [QuditShift.resetWireToBasis_pool]
      simp [tally_add, tally_singleton, isResetShift, QuditShift.gateLabel,
        Resource.GateLabel.builtin, Circuit.zEvent]) path
  simpa only [reset, QuditShift.resetToBasis, QuditShift.resetToBasisOn, id_eq,
    context_width, Nat.mul_comm] using counted

private theorem reset_measurements (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (P : KnownOrderProblem G) (count : Nat)
    (ux : UxAccess P) (slot : Fin count)
    (path : (reset base noQuantum P count ux slot).Path) :
    tally isMeasurement ((reset base noQuantum P count ux slot).resourcePool path) =
      totalQubits P := by
  have counted := range_observation (tally isMeasurement) (by simp [tally]) (tally_add
    isMeasurement) 1 (context base noQuantum P count).systemCount
    (fun wire => QuditShift.resetWireToBasis wire (resetCell base noQuantum P count slot wire)
      (resetLabel base noQuantum P count ux wire))
    (fun wire iteration => by
      rw [QuditShift.resetWireToBasis_pool]
      simp [tally_add, tally_singleton, isMeasurement, Circuit.zEvent]) path
  simpa only [reset, QuditShift.resetToBasis, QuditShift.resetToBasisOn, id_eq,
    context_width, mul_one] using counted

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (P : KnownOrderProblem G) (count : Nat)
    (B : UniformSuperposition.BinaryExpansion P.order) (ux : UxAccess P)

/-- Exactly one original opaque encoded group query executes for each requested sample. -/
theorem nativeFiniteCyclicBatch_run_query_count
    (path : (run base noQuantum P count B ux).code.Path) :
    ResourcePool.count (uxEvent P)
      ((run base noQuantum P count B ux).code.resourcePool path) = count := by
  have same := run_coordinate (uxEvent P)
    (by intro dimension; simp [uxEvent, Circuit.zEvent])
    (by intro dimension amount; simp [uxEvent]) base noQuantum P count B ux
    (by intro equality; cases equality) path
  simpa only [GateLevelAttempt.quantumCircuit_ux_count, mul_one] using same

/-- Every original paired inverse QFT contributes exactly its controlled-phase count. -/
theorem nativeFiniteCyclicBatch_run_controlledPhase_count
    (path : (run base noQuantum P count B ux).code.Path) :
    ResourcePool.count (.gate qftControlledPhaseLabel)
      ((run base noQuantum P count B ux).code.resourcePool path) =
        count * (orderWidth P * (orderWidth P - 1)) := by
  simpa only [GateLevelAttempt.quantumCircuit_controlledPhase_count] using
    gate_coordinate qftControlledPhaseLabel (by decide) base noQuantum P count B ux path

/-- The original two bit-reversal networks execute in every actual sample. -/
theorem nativeFiniteCyclicBatch_run_swap_count
    (path : (run base noQuantum P count B ux).code.Path) :
    ResourcePool.count (.gate (.builtin "swap"))
      ((run base noQuantum P count B ux).code.resourcePool path) =
        count * (2 * (orderWidth P / 2)) := by
  simpa only [GateLevelAttempt.quantumCircuit_swap_count] using
    gate_coordinate (.builtin "swap") (by decide) base noQuantum P count B ux path

/-- Only later samples execute both paid cyclic shifts on each existing bank wire. -/
theorem nativeFiniteCyclicBatch_run_resetShift_count
    (path : (run base noQuantum P count B ux).code.Path) :
    resetShiftCount ((run base noQuantum P count B ux).code.resourcePool path) =
      (count - 1) * (2 * totalQubits P) := by
  have same := run_observation (tally isResetShift) (by simp [tally]) (tally_add isResetShift)
    base noQuantum P count B ux (by simp [tally_singleton, isResetShift, BasisPreparation.event])
    0 (2 * totalQubits P) (fun slot path => by
      have counted := sample_tally isResetShift base noQuantum P count B ux slot
        (member_tally_zero isResetShift shift_off_elementary rfl rfl P rfl B ux) path
      simpa [isResetShift, Circuit.zEvent] using counted)
    (reset_shifts base noQuantum P count ux) path
  simpa only [resetShiftCount, Nat.mul_zero, Nat.zero_add] using same

/-- Each sample measures both exponent registers; only later samples add whole-bank reset Zs. -/
theorem nativeFiniteCyclicBatch_run_measurement_count
    (path : (run base noQuantum P count B ux).code.Path) :
    measurementCount ((run base noQuantum P count B ux).code.resourcePool path) =
      count * (2 * orderWidth P) + (count - 1) * totalQubits P := by
  have same := run_observation (tally isMeasurement) (by simp [tally]) (tally_add isMeasurement)
    base noQuantum P count B ux (by simp [tally_singleton, isMeasurement, BasisPreparation.event])
    (sampleWidth P) (totalQubits P) (fun slot path => by
      have counted := sample_tally isMeasurement base noQuantum P count B ux slot
        (member_tally_zero isMeasurement measurement_off_elementary rfl rfl P rfl B ux) path
      simpa [isMeasurement, Circuit.zEvent] using counted)
    (reset_measurements base noQuantum P count ux) path
  simpa only [measurementCount, sampleWidth, two_mul] using same

/-- The retained raw cells contribute exactly two original exponent widths per sample. -/
theorem nativeFiniteCyclicBatch_samplingSpace_classicalBits :
    SpacePool.count .classicalBits (samplingSpace P count) = count * (2 * orderWidth P) := by
  have clogTwo : Nat.clog 2 2 = 1 := by decide
  simp [samplingSpace, SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    CShape.bitWidth, clogTwo, sampleWidth, two_mul]

/-- The complete original bank contributes three widths of qubits and no other system dimension. -/
theorem nativeFiniteCyclicBatch_samplingSpace_quantumSystems (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension) (samplingSpace P count) =
      if 2 = dimension then 3 * orderWidth P else 0 := by
  simp [samplingSpace, SpacePool.count, SpacePool.ofShape, SpacePool.ofQuantumLayout,
    bankLayout, QubitLayout.toQuantumLayout_dimensionCount, totalQubits]
  split_ifs <;> omega

/-- The actual resident classical peak contains every raw sample and the whole caller. -/
theorem nativeFiniteCyclicBatch_run_resident_classicalBits
    (path : (run base noQuantum P count B ux).code.Path) :
    SpacePool.count .classicalBits
      ((run base noQuantum P count B ux).code.peakResidentSpace path) =
        count * (2 * orderWidth P) + SpacePool.count .classicalBits base.residentSpace := by
  rw [nativeFiniteCyclicBatch_run_resident, SpacePool.count_add,
    nativeFiniteCyclicBatch_samplingSpace_classicalBits]

/-- The actual resident quantum axes retain one whole bank alongside the original caller axes. -/
theorem nativeFiniteCyclicBatch_run_resident_quantumSystems (dimension : ℕ+)
    (path : (run base noQuantum P count B ux).code.Path) :
    SpacePool.count (.quantumSystems dimension)
      ((run base noQuantum P count B ux).code.peakResidentSpace path) =
        (if 2 = dimension then 3 * orderWidth P else 0) +
          SpacePool.count (.quantumSystems dimension) base.residentSpace := by
  rw [nativeFiniteCyclicBatch_run_resident, SpacePool.count_add,
    nativeFiniteCyclicBatch_samplingSpace_quantumSystems]

/-- The actual auxiliary classical peak contains every raw sample and the whole caller. -/
theorem nativeFiniteCyclicBatch_run_auxiliary_classicalBits
    (path : (run base noQuantum P count B ux).code.Path) :
    SpacePool.count .classicalBits
      ((run base noQuantum P count B ux).code.peakAuxiliarySpace path) =
        count * (2 * orderWidth P) + SpacePool.count .classicalBits base.auxiliarySpace := by
  rw [nativeFiniteCyclicBatch_run_auxiliary, SpacePool.count_add,
    nativeFiniteCyclicBatch_samplingSpace_classicalBits]

/-- The actual auxiliary quantum axes retain one whole bank alongside the original caller axes. -/
theorem nativeFiniteCyclicBatch_run_auxiliary_quantumSystems (dimension : ℕ+)
    (path : (run base noQuantum P count B ux).code.Path) :
    SpacePool.count (.quantumSystems dimension)
      ((run base noQuantum P count B ux).code.peakAuxiliarySpace path) =
        (if 2 = dimension then 3 * orderWidth P else 0) +
          SpacePool.count (.quantumSystems dimension) base.auxiliarySpace := by
  rw [nativeFiniteCyclicBatch_run_auxiliary, SpacePool.count_add,
    nativeFiniteCyclicBatch_samplingSpace_quantumSystems]

end

end QuantumAlg.FiniteCyclicDLP.Canonical.GateLevelAttempt.Native.Batch
