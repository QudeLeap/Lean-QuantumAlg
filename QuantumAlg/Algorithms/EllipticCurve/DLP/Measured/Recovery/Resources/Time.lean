/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Core.Execution.Time
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Path
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Depth
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates

/-!
# Time of the actual allocated streaming recovery run

Every component path is projected from the same complete run: allocation,
each finite sampling/checking attempt, and the one final paid option pack.
General event durations retain the pack and complete checked recovery. The
canonical quantum duration is zero on their actual classical instructions;
it still charges every gate and query in reset and converted sampling.

These are exact path identities, including count zero and zero-width banks.
No replacement run, execution restriction, success certificate or numeric
bound for all reset and converted sampling instructions is introduced.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Time

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.ClassicalAlgorithms.EllipticCurve (CurveSpec)
open QuantumAlg.ClassicalAlgorithms.Modular (ModulusSpec)
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
  (attemptEnvelope attemptEnvelope_count_eq_zero persistentAttempt attemptInto_pool_le
    sampledAttempt sampledAttempt_duration sampledRecoveryTail sampledRecoveryTail_duration)
open FiniteCyclicDLP (KnownOrderProblem orderWidth)
open scoped BigOperators

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

attribute [local irreducible] Recovery.PublicInput.Allocation.circuit
  Recovery.Initialization.newReset Recovery.Conversion.convertedStages BitWord.selectForCircuit

private lemma selected_quantumTime {gates : GateModel} {oracles : OracleModel}
    {allowAllocation : Bool} {pre post : RuntimeCtx .quantum}
    (code : Circuit (.quantum gates oracles) pre post allowAllocation)
    (path : (BitWord.selectForCircuit code).Path) :
    (BitWord.selectForCircuit code).quantumTime path =
      code.quantumTime ((BitWord.selectForCircuitPathEquiv code).symm path) := by
  have durations :
      (Resource.Event.quantumDuration :
        Resource.Event (.quantum gates oracles BitWord.model) → Nat) ∘
          BitWord.liftQuantumEvent =
        (Resource.Event.quantumDuration : Resource.Event (.quantum gates oracles) → Nat) := by
    funext event
    cases event with
    | classicalOperation impossible => cases impossible
    | classicalQuery impossible => cases impossible
    | gate coordinate => rfl
    | oracle coordinate => rfl
    | preparation dimension => rfl
    | measurement dimension => rfl
  have selected := BitWord.selectForCircuit_depth code Resource.Event.quantumDuration
    ((BitWord.selectForCircuitPathEquiv code).symm path)
  rw [Equiv.apply_symm_apply, durations] at selected
  exact selected

private lemma selected_embedded_seq_quantumTime {gates : GateModel}
    {oracles : OracleModel} {localCtx caller : RuntimeCtx .quantum}
    (placement : ContextEmbedding localCtx caller)
    (first second : Circuit (.quantum gates oracles) localCtx localCtx false)
    (path : (BitWord.selectForCircuit
      (Circuit.embed (allowAllocation := false) placement (first.seq second))).Path) :
    let placed := Circuit.embed (allowAllocation := false) placement (first.seq second)
    let original := (BitWord.selectForCircuitPathEquiv placed).symm path
    (BitWord.selectForCircuit placed).quantumTime path =
      first.quantumTime original.1 + second.quantumTime original.2 := by
  dsimp only
  let placed := Circuit.embed (allowAllocation := false) placement (first.seq second)
  let original := (BitWord.selectForCircuitPathEquiv placed).symm path
  have selected := selected_quantumTime placed path
  have embedded := Circuit.quantumTime_embed (allowAllocation := false) placement
    (first.seq second) original
  have serial := Circuit.quantumTime_seq first second original.1 original.2
  exact selected.trans (embedded.trans serial)

private lemma attempt_quantum_weight_zero {model : ExecutionModel} [BitWord.Selected model]
    {width scalarWidth : Nat} (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (attemptEnvelope model curve modulus) = 0 := by
  classical
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  by_cases operation : ∃ label, event = .classicalOperation label
  · obtain ⟨label, rfl⟩ := operation
    rfl
  · have zero := attemptEnvelope_count_eq_zero (model := model)
      event (by intro label same; exact operation ⟨label, same⟩) curve modulus
    exact False.elim ((Multiset.count_eq_zero.mp zero) present)

private lemma checker_quantumTime_zero {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (QuantumAlg.ClassicalRoutines.EllipticCurve.PointShape width))
    (path : (persistentAttempt curve modulus sample base target).Path) :
    (persistentAttempt curve modulus sample base target).quantumTime path = 0 := by
  have bounded := Circuit.depth_le_weightedCount_of_pool_le
    (persistentAttempt curve modulus sample base target) Resource.Event.quantumDuration
    (attemptEnvelope model curve modulus) path
    (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path)
  rw [attempt_quantum_weight_zero curve modulus] at bounded
  exact Nat.eq_zero_of_le_zero bounded

attribute [local irreducible] persistentAttempt

/-- Project the original sample path before specializing any concrete ECC context. -/
private def sampledAttemptSamplePath {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (QuantumAlg.ClassicalRoutines.EllipticCurve.PointShape width))
    (path : (sampledAttempt sampleCode curve modulus sample base target).Path) :
    sampleCode.Path := path.1

private lemma sampled_attempt_quantumTime {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (QuantumAlg.ClassicalRoutines.EllipticCurve.PointShape width))
    (path : (sampledAttempt sampleCode curve modulus sample base target).Path) :
    (sampledAttempt sampleCode curve modulus sample base target).quantumTime path =
      sampleCode.quantumTime path.1 := by
  have serial := sampledAttempt_duration sampleCode curve modulus sample base target
    Resource.Event.quantumDuration path
  have checked := checker_quantumTime_zero curve modulus sample base target path.2
  exact serial.trans ((congrArg (fun value : Nat => sampleCode.quantumTime path.1 + value)
    checked).trans (Nat.add_zero _))

private lemma sampled_tail_depth_sum {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (QuantumAlg.ClassicalRoutines.EllipticCurve.PointShape width))
    (duration : Resource.Event model → Nat)
    (path : (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    let attempt := sampledAttempt sampleCode curve modulus sample base target
    (sampledRecoveryTail sampleCode count curve modulus sample base target).depth duration path =
      (∑ index : Fin count, attempt.depth duration
        (Circuit.forRangeComponentPath count (fun _ => attempt) path.1.2 index)) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packOption scalarWidth)))) := by
  dsimp only
  let attempt := sampledAttempt sampleCode curve modulus sample base target
  have tailLaw := sampledRecoveryTail_duration sampleCode count curve modulus sample base target
    duration path
  have loopLaw := Circuit.forRange_depth_eq_sum count (fun _ => attempt) duration path.1.2
  exact tailLaw.trans (congrArg (fun value : Nat =>
    value + duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption scalarWidth))))) loopLaw)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

omit [Fact p.Prime] in
/-- The literal initial allocation emits its preparation events but no gate or query time. -/
lemma streamingRecovery_allocation_quantumTime (m : Nat)
    (path : (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E m)).Path) :
    (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E m)).quantumTime path = 0 :=
  (selected_quantumTime (Recovery.PublicInput.Allocation.circuit E m) path).trans
    (Recovery.PublicInput.Allocation.circuit_quantumTime E m _)

/-- Selection and the public placement preserve the same reset and converted child paths. -/
lemma streamingRecovery_round_quantumTime
    (path : (round E fieldTail problem points seed r coefficient).Path) :
    let body := Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed r
      points coefficient
    let placed := Circuit.embed (allowAllocation := false)
      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)) body
    let original := (BitWord.selectForCircuitPathEquiv placed).symm path
    (round E fieldTail problem points seed r coefficient).quantumTime path =
      (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).quantumTime
          original.1 +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).quantumTime original.2 := by
  exact selected_embedded_seq_quantumTime
    (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
    (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed)
    (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
      coefficient) path

variable (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Every real finite attempt and the final paid pack contribute their exact dependency depths.
-/
lemma streamingRecovery_run_depth (duration : Resource.Event Model → Nat)
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    let sampleCode := round E fieldTail problem points seed r coefficient
    let curve := ECDLP.Canonical.Layout.curveSpec E
    let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
    let sample := recoveryInput (orderWidth problem)
      (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth
        problem)))
    let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
    let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
    let attempt := sampledAttempt sampleCode curve modulus sample base target
    (run E fieldTail problem points seed r coefficient nontrivial count).code.depth duration path =
      (BitWord.selectForCircuit
        (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).depth duration path.1 +
        (∑ index : Fin count, attempt.depth duration
          (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index)) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := Model)
          (.nominalEncoding (.packOption (orderWidth problem))))) := by
  dsimp only
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
  let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
  have serial :
      (run E fieldTail problem points seed r coefficient nontrivial count).code.depth
        duration path =
      (BitWord.selectForCircuit
        (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).depth duration path.1 +
        (sampledRecoveryTail sampleCode count curve modulus sample base target).depth
          duration path.2 :=
    Circuit.depth_seq
      (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
      (sampledRecoveryTail sampleCode count curve modulus sample base target)
      duration path.1 path.2
  have native := sampled_tail_depth_sum sampleCode count curve modulus sample base target
    duration path.2
  exact serial.trans ((congrArg (fun value : Nat =>
    (BitWord.selectForCircuit
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).depth duration path.1 +
        value)
      native).trans (Nat.add_assoc _ _ _).symm)

attribute [local irreducible] Circuit.quantumTime Circuit.depth
  BitWord.selectForCircuitPathEquiv QuantumAlg.FiniteCyclicDLP.orderWidth
  QuantumAlg.FiniteCyclicDLP.oversampledOrder

/-- The actual checked attempt consumes its original complete checker path; its quantum time
vanishes by the original classical allowance, leaving the same reset and converted sample.
-/
lemma streamingRecovery_attempt_quantumTime
    (path : (sampledAttempt (round E fieldTail problem points seed r coefficient)
      (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
      (recoveryInput (orderWidth problem)
        (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth
          problem))))
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem))).Path) :
    let body := Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed r
      points coefficient
    let placed := Circuit.embed (allowAllocation := false)
      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)) body
    let original :
        (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).Path ×
          (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth
            problem))
            coefficient).Path :=
      (BitWord.selectForCircuitPathEquiv placed).symm
        (sampledAttemptSamplePath (round E fieldTail problem points seed r coefficient)
          (ECDLP.Canonical.Layout.curveSpec E)
          (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
          (recoveryInput (orderWidth problem)
            (PaidPacking.callerInput
              (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))))
          (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
          (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) path)
    (sampledAttempt (round E fieldTail problem points seed r coefficient)
      (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
      (recoveryInput (orderWidth problem)
        (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth
          problem))))
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem))).quantumTime path =
      (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).quantumTime
          original.1 +
        (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth problem))
          coefficient).quantumTime original.2 := by
  dsimp only
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
  let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
  have serial := sampled_attempt_quantumTime sampleCode curve modulus sample base target path
  exact serial.trans (streamingRecovery_round_quantumTime E fieldTail problem points seed r
    coefficient path.1)

/-- The full same run charges every reset and converted sampler at its actual finite-loop path.
The initial preparation, original native checker and final paid pack have zero quantum duration.
-/
lemma streamingRecovery_run_quantumTime
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    let sampleCode := round E fieldTail problem points seed r coefficient
    let curve := ECDLP.Canonical.Layout.curveSpec E
    let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
    let sample := recoveryInput (orderWidth problem)
      (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth
        problem)))
    let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
    let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
    let attempt := sampledAttempt sampleCode curve modulus sample base target
    let placed := Circuit.embed (allowAllocation := false)
      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
      (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed r points
        coefficient)
    let original : Fin count →
        (Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).Path ×
          (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth
            problem))
            coefficient).Path := fun index =>
      (BitWord.selectForCircuitPathEquiv placed).symm
        (sampledAttemptSamplePath sampleCode curve modulus sample base target
          (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index))
    (run E fieldTail problem points seed r coefficient nontrivial count).code.quantumTime path =
      ∑ index : Fin count,
        ((Recovery.Initialization.newReset E fieldTail (orderWidth problem) seed).quantumTime
            (original index).1 +
          (Recovery.Conversion.convertedStages E r points (Recovery.Layout.order (orderWidth
            problem))
            coefficient).quantumTime (original index).2) := by
  dsimp only
  let sampleCode := round E fieldTail problem points seed r coefficient
  let curve := ECDLP.Canonical.Layout.curveSpec E
  let modulus := FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial
  let sample := recoveryInput (orderWidth problem)
    (PaidPacking.callerInput (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem)))
  let base := Recovery.PublicInput.contextBaseRef E (orderWidth problem)
  let target := Recovery.PublicInput.contextTargetRef E (orderWidth problem)
  let attempt := sampledAttempt sampleCode curve modulus sample base target
  let total := ∑ index : Fin count, attempt.quantumTime
    (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index)
  have serial :
      (run E fieldTail problem points seed r coefficient nontrivial count).code.quantumTime path =
        (BitWord.selectForCircuit
          (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).quantumTime path.1 +
          total + 0 := by
    simpa only [total, Circuit.quantumTime, Resource.Event.quantumDuration_classicalOperation] using
      streamingRecovery_run_depth E fieldTail problem points seed r coefficient nontrivial count
        Resource.Event.quantumDuration path
  have allocationZero := streamingRecovery_allocation_quantumTime E (orderWidth problem) path.1
  have reduced :
      (BitWord.selectForCircuit
        (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).quantumTime path.1 +
        total + 0 = total :=
    (congrArg (fun value : Nat => value + total + 0) allocationZero).trans
      ((congrArg (fun value : Nat => value + 0) (Nat.zero_add total)).trans (Nat.add_zero total))
  refine (serial.trans reduced).trans ?_
  apply Finset.sum_congr rfl
  intro index _
  exact streamingRecovery_attempt_quantumTime E fieldTail problem points seed r coefficient
    nontrivial (Circuit.forRangeComponentPath count (fun _ => attempt) path.2.1.2 index)

end

end ExecutionContract.Time
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
