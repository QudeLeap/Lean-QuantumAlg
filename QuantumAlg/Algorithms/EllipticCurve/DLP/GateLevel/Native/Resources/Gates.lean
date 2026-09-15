/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Coordinates

/-!
# Paid reset gates and measurements on the complete ECDLP path

Each wire is measured and receives its outcome correction and prescribed basis
shift in every round. Both shifts are native one-wire gate events, including
zero shifts. They augment the original Hadamard/X/rotation-Y classifier.
The original member and classical checker contribute no reset-shift or
measurement label. All counts below concern the complete actual recovery run.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

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

/-- Single-qubit gate families used by this execution: original elementary gates
and reset shifts. -/
def singleQubitGateCount (pool : ResourcePool .quantum) : Nat :=
  GateLevelResources.singleQubitCount pool + resetShiftCount pool

private theorem range_tally {ctx : RuntimeCtx .quantum}
    (test : Resource.Event .quantum → Bool) (amount count : Nat)
    (body : Fin count → Circuit ctx ctx)
    (same : ∀ index path, tally test ((body index).resourcePool path) = amount)
    (path : (Circuit.forRange count body).Path) :
    tally test ((Circuit.forRange count body).resourcePool path) = count * amount := by
  induction count with
  | zero => simp [Circuit.forRange, Circuit.resourcePool, Circuit.eventTrace,
      ResourcePool.ofList, tally]
  | succ count ih =>
      change tally test (ResourcePool.ofList ((body 0).eventTrace path.1 ++
        (Circuit.forRange count (fun index => body index.succ)).eventTrace path.2)) = _
      erw [ResourcePool.ofList_append, tally_add, same,
        ih (fun index => body index.succ) (fun index => same index.succ)]
      simp [Nat.add_mul, Nat.add_comm]

private theorem attempt_tally_zero (test : Resource.Event .quantum → Bool)
    (offClassical : ∀ label, test (.classicalOperation label) = false)
    {width scalarWidth : Nat} (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (pool : ResourcePool .quantum) (bounded : pool ≤ attemptEnvelope .quantum curve modulus) :
    tally test pool = 0 := by
  apply Multiset.countP_eq_zero.mpr
  intro event member observed
  have outside : ∀ label, event ≠ .classicalOperation label := by
    intro label equality
    rw [equality, offClassical] at observed
    cases observed
  have upper := (ResourcePool.le_iff_count.mp bounded) event
  rw [attemptEnvelope_count_eq_zero event outside] at upper
  have positive : 0 < ResourcePool.count event pool := Multiset.count_pos.mpr member
  omega

private theorem sampled_tally {ctx : RuntimeCtx .quantum}
    (test : Resource.Event .quantum → Bool)
    (offClassical : ∀ label, test (.classicalOperation label) = false)
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (amount : Nat) (same : ∀ path, tally test (code.resourcePool path) = amount)
    (path : (sampledAttempt code supported curve modulus sample base target).Path) :
    tally test
      ((sampledAttempt code supported curve modulus sample base target).resourcePool path) =
        amount := by
  rw [Circuit.resourcePool, sampledAttempt_eventTrace, ResourcePool.ofList_append, tally_add]
  erw [same]
  have absent := attempt_tally_zero test offClassical curve modulus _
    (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2)
  erw [absent, add_zero]

private theorem tail_tally {ctx : RuntimeCtx .quantum}
    (test : Resource.Event .quantum → Bool)
    (offClassical : ∀ label, test (.classicalOperation label) = false)
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (count amount : Nat) (same : ∀ path, tally test (code.resourcePool path) = amount)
    (path : (sampledRecoveryTail code supported count curve modulus sample base target).Path) :
    tally test
      ((sampledRecoveryTail code supported count curve modulus sample base target).resourcePool
        path) = count * amount := by
  rw [Circuit.resourcePool, sampledRecoveryTail_eventTrace, ResourcePool.ofList_append, tally_add]
  have loop := range_tally test amount count
    (fun _ => sampledAttempt code supported curve modulus sample base target)
    (fun _ => sampled_tally test offClassical code supported curve modulus sample base target
      amount same) path.1.2
  erw [loop]
  simp [tally_singleton, offClassical]

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem member_tally_zero (test : Resource.Event .quantum → Bool)
    (offElementary : ∀ event, UniformSuperposition.elementaryEvent event → test event = false)
    (offPhase : test (.gate qftControlledPhaseLabel) = false)
    (offSwap : test (.gate (.builtin "swap")) = false)
    (I : ECDLPInstance E) (offQuery : test (uPQEvent I) = false)
    (B : OrderExpansion (problem I).order) (A : Access I) :
    tally test (GateLevelAttempt.quantumCircuit I B A).eventCost = 0 := by
  have prepZero : tally test (B.paddedPreparation (problem I)).eventCost = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro event member observed
    have notElementary : ¬ UniformSuperposition.elementaryEvent event := by
      intro elementary
      rw [offElementary event elementary] at observed
      cases observed
    exact (Multiset.count_eq_zero.mp
      (B.paddedPreparation_count_zero_of_not_elementary (problem I) event notElementary)) member
  have hadamard : test (.gate (.builtin "hadamard")) = false :=
    offElementary _ (by simp [UniformSuperposition.elementaryEvent])
  rw [GateLevelResources.quantumCircuit_eventCost,
    GateLevelResources.inverseQFTCircuit_eventCost_eq_pair]
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
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I)
    (offMember : tally test (GateLevelAttempt.quantumCircuit I B A).eventCost = 0)
    (path : (sample base noQuantum I B A).Path) :
    tally test ((sample base noQuantum I B A).resourcePool path) =
      sampleWidth I * (if test (Circuit.zEvent 2) then 1 else 0) := by
  rw [Circuit.resourcePool, nativeECDLP_sample_eventTrace, ResourcePool.ofList_append,
    tally_add, UnitaryCircuit.ofList_eventTrace_eq_eventCost, offMember, zero_add]
  simp [tally_list, List.countP_replicate]

private theorem reset_shifts (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (I : ECDLPInstance E) (path : (reset base noQuantum I).Path) :
    tally isResetShift ((reset base noQuantum I).resourcePool path) = 2 * Layout.totalQubits I := by
  have counted := range_tally isResetShift 2 (context base noQuantum I).systemCount
    (fun wire => QuditShift.resetWireToBasis wire (resetCell base noQuantum I wire)
      (resetLabel base noQuantum I wire))
    (fun wire iteration => by
      rw [QuditShift.resetWireToBasis_pool]
      simp [tally_add, tally_singleton, isResetShift, QuditShift.gateLabel,
        Resource.GateLabel.builtin, Circuit.zEvent]) path
  simpa only [reset, QuditShift.resetToBasis, QuditShift.resetToBasisOn, id_eq,
    context_width, Nat.mul_comm] using counted

private theorem reset_measurements (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (path : (reset base noQuantum I).Path) :
    tally isMeasurement ((reset base noQuantum I).resourcePool path) = Layout.totalQubits I := by
  have counted := range_tally isMeasurement 1 (context base noQuantum I).systemCount
    (fun wire => QuditShift.resetWireToBasis wire (resetCell base noQuantum I wire)
      (resetLabel base noQuantum I wire))
    (fun wire iteration => by
      rw [QuditShift.resetWireToBasis_pool]
      simp [tally_add, tally_singleton, isMeasurement, Circuit.zEvent]) path
  simpa only [reset, QuditShift.resetToBasis, QuditShift.resetToBasisOn, id_eq,
    context_width, mul_one] using counted

attribute [local irreducible] underPersistent

private theorem recovery_tally (test : Resource.Event .quantum → Bool)
    (offClassical : ∀ label, test (.classicalOperation label) = false)
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (offPrepared : test (preparation I).event = false)
    (B : OrderExpansion (problem I).order) (A : Access I) (count amount : Nat)
    (same : ∀ path, tally test ((reusedSample base noQuantum I B A).resourcePool path) = amount)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    tally test
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * amount := by
  change tally test (ResourcePool.ofList ((allocate base noQuantum I).eventTrace path.1 ++
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)).eventTrace
        path.2)) = _
  rw [ResourcePool.ofList_append, tally_add, nativeECDLP_allocate_events]
  have tail := tail_tally test offClassical (reusedSample base noQuantum I B A)
    (nativeECDLP_reusedSample_isLocal base noQuantum I B A)
    (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
    (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint) count amount
    same path.2
  erw [tail]
  simp [tally_singleton, offPrepared]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))

/-- Every actual round performs both paid shifts on every original wire, including zero shifts. -/
theorem nativeECDLP_recovery_resetShift_count
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    resetShiftCount
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * (2 * Layout.totalQubits I) := by
  apply recovery_tally isResetShift (fun _ => rfl) base noQuantum I rfl B A count
    (2 * Layout.totalQubits I) ?_ basePoint targetPoint path
  intro iteration
  change tally isResetShift (ResourcePool.ofList ((reset base noQuantum I).eventTrace iteration.1 ++
    (sample base noQuantum I B A).eventTrace iteration.2)) = _
  rw [ResourcePool.ofList_append, tally_add]
  erw [reset_shifts, sample_tally isResetShift base noQuantum I B A
    (member_tally_zero isResetShift shift_off_elementary rfl rfl I rfl B A)]
  simp [isResetShift, Circuit.zEvent]

/-- Real reset measurements and exponent readouts both contribute in every round. -/
theorem nativeECDLP_recovery_measurement_count
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    measurementCount
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) =
        count * (Layout.totalQubits I + 2 * FiniteCyclicDLP.orderWidth (problem I)) := by
  apply recovery_tally isMeasurement (fun _ => rfl) base noQuantum I rfl B A count
    (Layout.totalQubits I + 2 * FiniteCyclicDLP.orderWidth (problem I)) ?_
    basePoint targetPoint path
  intro iteration
  change tally isMeasurement (ResourcePool.ofList
    ((reset base noQuantum I).eventTrace iteration.1 ++
      (sample base noQuantum I B A).eventTrace iteration.2)) = _
  rw [ResourcePool.ofList_append, tally_add]
  erw [reset_measurements, sample_tally isMeasurement base noQuantum I B A
    (member_tally_zero isMeasurement measurement_off_elementary rfl rfl I rfl B A)]
  simp [isMeasurement, Circuit.zEvent, sampleWidth, two_mul]

/-- Total native single-qubit gates include the literal preparation/QFT gates
and paid reset shifts. -/
theorem nativeECDLP_recovery_singleQubitGate_count_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    singleQubitGateCount
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) ≤
        count * (2 * FiniteCyclicDLP.orderWidth (problem I) +
          2 * B.singleQubitBound + 2 * Layout.totalQubits I) := by
  unfold singleQubitGateCount
  rw [nativeECDLP_recovery_resetShift_count]
  have bounded := Nat.add_le_add_right
    (nativeECDLP_recovery_singleQubit_count_le base noQuantum I B A count
      basePoint targetPoint path) (count * (2 * Layout.totalQubits I))
  simpa only [Nat.mul_add] using bounded

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
