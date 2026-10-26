/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Program
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Attempt.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Same-path composition of actual three-round sampling and paid checked recovery

The actual allocating sampler is followed by the original nearest decoder,
candidate verification and first-success latch. Every declared attempt pays
both components. The seven initial retained destinations emit no native event;
the one final option pack remains charged after all attempts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Recovery.Parameters

noncomputable section

open Execution
open ClassicalRoutines
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Recovery.Parameters ctx)

private lemma sequential_pool {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {allocation : Bool}
    (first : Circuit model pre mid allocation) (second : Circuit model mid post allocation)
    (path : (first.seq second).Path) :
    (first.seq second).resourcePool path =
      first.resourcePool path.1 + second.resourcePool path.2 := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) = _
  exact ResourcePool.ofList_append _ _

private lemma sequential_depth {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {allocation : Bool}
    (first : Circuit model pre mid allocation) (second : Circuit model mid post allocation)
    (duration : Resource.Event model → Nat) (path : (first.seq second).Path) :
    (first.seq second).depth duration path =
      first.depth duration path.1 + second.depth duration path.2 :=
  Circuit.depth_seq first second duration path.1 path.2

private lemma sequential_depth_right_zero {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {allocation : Bool}
    (first : Circuit model pre mid allocation) (second : Circuit model mid post allocation)
    (duration : Resource.Event model → Nat) (limit : Nat)
    (firstBound : ∀ path, first.depth duration path ≤ limit)
    (secondZero : ∀ path, second.depth duration path = 0)
    (path : (first.seq second).Path) : (first.seq second).depth duration path ≤ limit := by
  exact (sequential_depth first second duration path).le.trans
    ((Nat.add_le_add (firstBound path.1) (secondZero path.2).le).trans_eq
      (Nat.add_zero limit))

private lemma sequential_depth_left_zero {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {allocation : Bool}
    (first : Circuit model pre mid allocation) (second : Circuit model mid post allocation)
    (duration : Resource.Event model → Nat) (limit : Nat)
    (firstZero : ∀ path, first.depth duration path = 0)
    (secondBound : ∀ path, second.depth duration path ≤ limit)
    (path : (first.seq second).Path) : (first.seq second).depth duration path ≤ limit := by
  exact (sequential_depth first second duration path).le.trans
    ((Nat.add_le_add (firstZero path.1).le (secondBound path.2)).trans_eq
      (Nat.zero_add limit))

private lemma repeated_depth_upper {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    {allocation : Bool} (code : Circuit model inner inner allocation)
    (duration : Resource.Event model → Nat) (limit : Nat)
    (bounded : ∀ path, code.depth duration path ≤ limit)
    (count : Nat) (path : (Circuit.forRange count (fun _ => code)).Path) :
    (Circuit.forRange count (fun _ => code)).depth duration path ≤ count * limit := by
  have actual := Circuit.forRange_depth_le_sum count (fun _ => code)
    duration (fun _ => limit) (fun _ current => bounded current) path
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using actual

private lemma persistentPack_quantumTime_zero {caller : RuntimeCtx .quantum}
    (width scalarWidth : Nat)
    (path : (EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      caller width scalarWidth).Path) :
    (EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      caller width scalarWidth).depth Resource.Event.quantumDuration path = 0 :=
  EllipticCurve.CandidateCheck.Native.packBatchResult_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    caller width scalarWidth Resource.Event.quantumDuration path

private lemma count_zero_of_pool_le {model : ExecutionModel} (event : Resource.Event model)
    (actual budget : ResourcePool model) (bounded : actual ≤ budget)
    (zero : ResourcePool.count event budget = 0) : ResourcePool.count event actual = 0 := by
  have counted := (ResourcePool.le_iff_count.mp bounded) event
  rw [zero] at counted
  exact Nat.eq_zero_of_le_zero counted

private lemma repeated_count_upper {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    {allocation : Bool} (code : Circuit model inner inner allocation)
    (event : Resource.Event model) (limit : Nat)
    (bounded : ∀ path, ResourcePool.count event (code.resourcePool path) ≤ limit)
    (count : Nat) (path : (Circuit.forRange count (fun _ => code)).Path) :
    ResourcePool.count event ((Circuit.forRange count (fun _ => code)).resourcePool path) ≤
      count * limit := by
  induction count with
  | zero =>
      change ResourcePool.count event (0 : ResourcePool model) ≤ 0 * limit
      simp only [ResourcePool.count_zero, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
      change ResourcePool.count event (code.resourcePool path.1 +
        (Circuit.forRange count (fun _ => code)).resourcePool path.2) ≤ _
      rw [ResourcePool.count_add, Nat.succ_mul]
      have first := bounded path.1
      have rest := ih path.2
      omega

private lemma repeated_weight_upper {model : ExecutionModel} {inner : RuntimeCtx model.kind}
    {allocation : Bool} (code : Circuit model inner inner allocation)
    (weight : Resource.Event model → Nat) (limit : Nat)
    (bounded : ∀ path, ResourcePool.weightedCount weight (code.resourcePool path) ≤ limit)
    (count : Nat) (path : (Circuit.forRange count (fun _ => code)).Path) :
    ResourcePool.weightedCount weight
      ((Circuit.forRange count (fun _ => code)).resourcePool path) ≤ count * limit := by
  induction count with
  | zero =>
      change ResourcePool.weightedCount weight (0 : ResourcePool model) ≤ 0 * limit
      simp only [ResourcePool.weightedCount_zero, Nat.zero_mul, Nat.le_refl]
  | succ count ih =>
      change ResourcePool.weightedCount weight (code.resourcePool path.1 +
        (Circuit.forRange count (fun _ => code)).resourcePool path.2) ≤ _
      rw [ResourcePool.weightedCount_add, Nat.succ_mul]
      have first := bounded path.1
      have rest := ih path.2
      omega

/-- The original independent allowance includes decoder, full checker and actual shared latch. -/
def checkerBudget : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) :=
  ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope
    (.quantum AlgorithmGate.model .empty BitWord.model services) original.curve original.order

private lemma nearestPreparation_count_zero {model : ExecutionModel} [BitWord.Selected model]
    {width : Nat} (event : Resource.Event model)
    (outside : ∀ label, event ≠ .classicalOperation label)
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (originalZero : ResourcePool.count event (preparationEnvelope model spec) = 0) :
    ResourcePool.count event
      (FiniteCyclicDLP.RawRecovery.Nearest.preparationEnvelope model spec) = 0 := by
  have scales : ResourcePool.count event (ResourcePool.ofList
      (FiniteCyclicDLP.RawRecovery.Nearest.scaleBodyEvents (model := model) width)) = 0 := by
    simp [FiniteCyclicDLP.RawRecovery.Nearest.scaleBodyEvents,
      ResourcePool.ofList, ResourcePool.count, outside]
  simp only [preparationEnvelope, ResourcePool.count_add] at originalZero
  simp only [FiniteCyclicDLP.RawRecovery.Nearest.preparationEnvelope,
    ResourcePool.count_add, scales]
  omega

/-- The paid nearest prefix and every original checking stage contain only classical labels. -/
lemma checker_count_zero
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) :
    ResourcePool.count event (original.checkerBudget (services := services)) = 0 := by
  have old := EllipticCurve.CandidateCheck.Native.attemptEnvelope_count_eq_zero
    event outside original.curve original.order
  simp only [EllipticCurve.CandidateCheck.Native.attemptEnvelope,
    FiniteCyclicDLP.RawRecovery.Native.singleExposureEnvelope, ResourcePool.count_add] at old
  have originalPreparation : ResourcePool.count event
      (preparationEnvelope (.quantum AlgorithmGate.model .empty BitWord.model services)
        original.order) = 0 := by omega
  simp only [checkerBudget, EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope,
    FiniteCyclicDLP.RawRecovery.Nearest.singleExposureEnvelope, ResourcePool.count_add,
    nearestPreparation_count_zero event outside original.order originalPreparation]
  omega

private lemma pool_not_mem_of_count_zero {model : ExecutionModel}
    (event : Resource.Event model) (pool : ResourcePool model)
    (zero : ResourcePool.count event pool = 0) : event ∉ pool := by
  exact Multiset.count_eq_zero.mp zero

attribute [local irreducible] checkerBudget ResourcePool.count ResourcePool.weightedCount

lemma checker_quantum_weight_zero :
    ResourcePool.weightedCount Resource.Event.quantumDuration (original.checkerBudget (services
      := services)) = 0 := by
  classical
  refine ResourcePool.weightedCount_eq_zero_of_mem
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    Resource.Event.quantumDuration (original.checkerBudget (services := services)) ?_
  intro event present
  by_cases operation : ∃ label, event = .classicalOperation label
  · obtain ⟨label, rfl⟩ := operation
    rfl
  · have zero := original.checker_count_zero (services := services) event
      (by intro label same; exact operation ⟨label, same⟩)
    exact False.elim
      (pool_not_mem_of_count_zero event (original.checkerBudget (services := services)) zero
        present)

private lemma persistentChecker_pool_le {model : ExecutionModel} [BitWord.Selected model]
    {caller : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef caller (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef caller (EllipticCurve.PointShape width))
    (path : (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).Path) :
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).resourcePool path ≤
        EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope model curve modulus := by
  exact EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := model) curve modulus
    (EllipticCurve.CandidateCheck.Native.persistentInput width scalarWidth sample)
    (EllipticCurve.CandidateCheck.Native.persistentInput width scalarWidth base)
    (EllipticCurve.CandidateCheck.Native.persistentInput width scalarWidth target)
    (EllipticCurve.CandidateCheck.Native.persistentInverseSuccess caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentCandidate caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentReconstruction caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentScalar caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentTargetAccepted caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentAccepted caller width scalarWidth)
    (EllipticCurve.CandidateCheck.Native.persistentSelected caller width scalarWidth) path

attribute [local irreducible] EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
-- Fixed-width applications use the named actual ledger and independent allowance.
attribute [local irreducible] EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope
attribute [local irreducible] Circuit.resourcePool

lemma checker_pool_le
    (path : (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler) original.base original.target).Path) :
    (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler)
      original.base original.target).resourcePool path ≤ (original.checkerBudget (services :=
        services)) := by
  have actual := @persistentChecker_pool_le
    (.quantum AlgorithmGate.model .empty BitWord.model services)
    (BitWord.selectedQuantum AlgorithmGate.model .empty services) ctx 256 260
    original.curve original.order (Recovery.pairedInput original.sampler)
    original.base original.target path
  simpa only [checkerBudget] using actual

attribute [local irreducible] Circuit.depth

lemma checker_quantumTime_zero
    (path : (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler) original.base original.target).Path) :
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler)
      original.base original.target).depth Resource.Event.quantumDuration path = 0 := by
  have bounded := Circuit.depth_le_weightedCount_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler) original.base original.target)
    Resource.Event.quantumDuration (original.checkerBudget (services := services)) path
    (original.checker_pool_le (services := services) path)
  rw [original.checker_quantum_weight_zero (services := services)] at bounded
  exact Nat.eq_zero_of_le_zero bounded

private lemma attempt_pool (path : (original.attempt (services := services)).Path) :
    (original.attempt (services := services)).resourcePool path =
      (original.sample (services := services)).resourcePool path.1 +
        (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          original.curve original.order (Recovery.pairedInput original.sampler)
          original.base original.target).resourcePool path.2 :=
  sequential_pool (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (original.sample (services := services))
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      original.curve original.order (Recovery.pairedInput original.sampler)
      original.base original.target) path

private lemma run_pool (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.resourcePool path =
      (EllipticCurve.CandidateCheck.Native.retainPersistent
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260).resourcePool path.1.1 +
          (original.attempts (services := services) 3).resourcePool path.1.2 +
        (EllipticCurve.CandidateCheck.Native.packBatchResult
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          ctx 256 260).resourcePool path.2 := by
  have outer := sequential_pool
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ((EllipticCurve.CandidateCheck.Native.retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).seq
        (original.attempts (services := services) 3))
    (EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260) path
  have inner := sequential_pool
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (EllipticCurve.CandidateCheck.Native.retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
    (original.attempts (services := services) 3) path.1
  exact outer.trans (congrArg
    (fun pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) =>
      pool + (EllipticCurve.CandidateCheck.Native.packBatchResult
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260).resourcePool path.2) inner)

private lemma pack_nonclassical_zero
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label)
    (path : (EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).Path) :
    ResourcePool.count event ((EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260).resourcePool path) = 0 := by
  rw [EllipticCurve.CandidateCheck.Native.packBatchResult_resourcePool]
  change ResourcePool.count event (ResourcePool.singleton
    (.classicalOperation (BitWord.selectedCoordinate
      (execution := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.nominalEncoding (.packOption 260))))) = 0
  exact ResourcePool.count_singleton_of_ne (outside _) 1

lemma attempt_nonclassical_count_le
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.count event ((original.sample (services := services)).resourcePool path) ≤
        sampleBudget)
    (path : (original.attempt (services := services)).Path) :
    ResourcePool.count event ((original.attempt (services := services)).resourcePool path) ≤
      sampleBudget := by
  have checked := count_zero_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) event _ _
    (original.checker_pool_le (services := services) path.2)
    (original.checker_count_zero (services := services) event outside)
  rw [original.attempt_pool (services := services), ResourcePool.count_add, checked, Nat.add_zero]
  exact sampleBound path.1

lemma attempts_nonclassical_count_le
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.count event ((original.sample (services := services)).resourcePool path) ≤
        sampleBudget)
    (count : Nat) (path : (original.attempts (services := services) count).Path) :
    ResourcePool.count event ((original.attempts (services := services) count).resourcePool path) ≤
      count * sampleBudget := by
  exact repeated_count_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (original.attempt (services := services)) event sampleBudget
    (fun current => original.attempt_nonclassical_count_le (services := services)
      event outside sampleBudget sampleBound current) count path

/-- All three real attempts retain the same nonclassical allowance; checker labels stay separate. -/
lemma run_nonclassical_count_le
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.count event ((original.sample (services := services)).resourcePool path) ≤
        sampleBudget)
    (path : (original.run (services := services)).code.Path) :
    ResourcePool.count event ((original.run (services := services)).code.resourcePool path) ≤ 3
      * sampleBudget := by
  rw [original.run_pool (services := services)]
  rw [ResourcePool.count_add, ResourcePool.count_add,
    EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    pack_nonclassical_zero event outside path.2]
  simpa only [ResourcePool.count_zero, Nat.zero_add, Nat.add_zero] using
      original.attempts_nonclassical_count_le (services := services) event outside sampleBudget
        sampleBound 3 path.1.2

lemma attempt_nonclassical_count
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) (amount : Nat)
    (sampleExact : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.count event ((original.sample (services := services)).resourcePool path) =
        amount)
    (path : (original.attempt (services := services)).Path) :
    ResourcePool.count event ((original.attempt (services := services)).resourcePool path) =
      amount := by
  have checked := count_zero_of_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) event _ _
    (original.checker_pool_le (services := services) path.2)
    (original.checker_count_zero (services := services) event outside)
  rw [original.attempt_pool (services := services), ResourcePool.count_add, checked, Nat.add_zero]
  exact sampleExact path.1

lemma run_nonclassical_count
    (event : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services))
    (outside : ∀ label, event ≠ .classicalOperation label) (amount : Nat)
    (sampleExact : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.count event ((original.sample (services := services)).resourcePool path) =
        amount)
    (path : (original.run (services := services)).code.Path) :
    ResourcePool.count event ((original.run (services := services)).code.resourcePool path) = 3
      * amount := by
  have attempts := Circuit.forRange_event_count event 3 (fun _ => (original.attempt (services :=
    services))) amount
    (fun _ current => original.attempt_nonclassical_count (services := services) event outside
      amount sampleExact current)
    path.1.2
  rw [original.run_pool (services := services)]
  rw [ResourcePool.count_add, ResourcePool.count_add,
    EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    pack_nonclassical_zero event outside path.2]
  simpa only [Recovery.Parameters.attempts, ResourcePool.count_zero, Nat.zero_add,
    Nat.add_zero] using attempts

lemma attempt_quantumTime_le (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      (original.sample (services := services)).depth Resource.Event.quantumDuration path ≤
        sampleBudget)
    (path : (original.attempt (services := services)).Path) :
    (original.attempt (services := services)).depth Resource.Event.quantumDuration path ≤
      sampleBudget := by
  exact sequential_depth_right_zero
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (original.sample (services := services))
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput original.sampler) original.base original.target)
    Resource.Event.quantumDuration sampleBudget sampleBound
    (fun current => original.checker_quantumTime_zero (services := services) current) path

lemma run_quantumTime_le (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      (original.sample (services := services)).depth Resource.Event.quantumDuration path ≤
        sampleBudget)
    (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.depth Resource.Event.quantumDuration path ≤ 3 *
      sampleBudget := by
  refine sequential_depth_right_zero
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ((EllipticCurve.CandidateCheck.Native.retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).seq
        (original.attempts (services := services) 3))
    (EllipticCurve.CandidateCheck.Native.packBatchResult
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
    Resource.Event.quantumDuration (3 * sampleBudget) ?_
    (fun current => persistentPack_quantumTime_zero (services := services) 256 260 current) path
  intro current
  refine sequential_depth_left_zero
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (EllipticCurve.CandidateCheck.Native.retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260)
    (original.attempts (services := services) 3)
    Resource.Event.quantumDuration (3 * sampleBudget)
    (fun initial => EllipticCurve.CandidateCheck.Native.retainPersistent_depth
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260 Resource.Event.quantumDuration initial) ?_ current
  intro repeated
  exact repeated_depth_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (original.attempt (services := services)) Resource.Event.quantumDuration sampleBudget
    (fun attempt => original.attempt_quantumTime_le (services := services) sampleBudget
      sampleBound attempt) 3 repeated

lemma attempt_weight_le
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services) → Nat)
    (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.weightedCount weight ((original.sample (services := services)).resourcePool
        path) ≤ sampleBudget)
    (path : (original.attempt (services := services)).Path) :
    ResourcePool.weightedCount weight ((original.attempt (services := services)).resourcePool
      path) ≤
      sampleBudget + ResourcePool.weightedCount weight (original.checkerBudget (services :=
        services)) := by
  have sample := sampleBound path.1
  have checker := ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    weight (original.checker_pool_le (services := services) path.2)
  rw [original.attempt_pool (services := services), ResourcePool.weightedCount_add]
  exact Nat.add_le_add sample checker

lemma attempts_weight_le
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services) → Nat)
    (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.weightedCount weight ((original.sample (services := services)).resourcePool
        path) ≤ sampleBudget)
    (count : Nat) (path : (original.attempts (services := services) count).Path) :
    ResourcePool.weightedCount weight ((original.attempts (services := services)
      count).resourcePool path) ≤
      count * (sampleBudget + ResourcePool.weightedCount weight (original.checkerBudget
        (services := services))) := by
  exact repeated_weight_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (original.attempt (services := services)) weight
    (sampleBudget + ResourcePool.weightedCount weight (original.checkerBudget
      (services := services)))
    (fun current => original.attempt_weight_le (services := services) weight sampleBudget
      sampleBound current) count path

/-- Every actual stage is paid, including the final pack after all three attempts. -/
lemma run_weight_le
    (weight : Resource.Event (.quantum AlgorithmGate.model .empty BitWord.model services) → Nat)
    (sampleBudget : Nat)
    (sampleBound : ∀ path : (original.sample (services := services)).Path,
      ResourcePool.weightedCount weight ((original.sample (services := services)).resourcePool
        path) ≤ sampleBudget)
    (path : (original.run (services := services)).code.Path) :
    ResourcePool.weightedCount weight ((original.run (services := services)).code.resourcePool
      path) ≤
      3 * (sampleBudget + ResourcePool.weightedCount weight (original.checkerBudget (services :=
        services))) +
        weight (.classicalOperation (BitWord.selectedCoordinate
          (execution := .quantum AlgorithmGate.model .empty BitWord.model services)
          (.nominalEncoding (.packOption 260)))) := by
  have attempts := original.attempts_weight_le (services := services) weight sampleBudget
    sampleBound 3 path.1.2
  rw [original.run_pool (services := services)]
  rw [ResourcePool.weightedCount_add, ResourcePool.weightedCount_add,
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.weightedCount_zero,
    ClassicalRoutines.EllipticCurve.CandidateCheck.Native.packBatchResult_resourcePool,
    ResourcePool.weightedCount_ofList, List.map_singleton, List.sum_singleton, Nat.zero_add]
  exact Nat.add_le_add_right attempts _

end

end Recovery.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
