/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Resources
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Resources.Bounds
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Resources.Numeric

/-!
# Same-path bounds for the real fresh-feedback recovery factory

The actual restart precedes the allocating thirty-four-window sampler and the
original explicit seven-destination nearest checker. One lexical feedback
scope surrounds all attempts and exits before the final option pack.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalWorkspace ClassicalRoutines

private lemma nearestEnvelope_count_zero {model : ExecutionModel} [BitWord.Selected model]
    {width scalarWidth : Nat} (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (event : Resource.Event model) (outside : ∀ label, event ≠ .classicalOperation label) :
    ResourcePool.count event
      (EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope model curve modulus) = 0 := by
  have old := EllipticCurve.CandidateCheck.Native.attemptEnvelope_count_eq_zero
    event outside curve modulus
  simp only [EllipticCurve.CandidateCheck.Native.attemptEnvelope,
    FiniteCyclicDLP.RawRecovery.Native.singleExposureEnvelope, ResourcePool.count_add] at old
  have preparation : ResourcePool.count event
      (FiniteCyclicDLP.RawRecovery.Native.preparationEnvelope model modulus) = 0 := by omega
  simp only [EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope,
    FiniteCyclicDLP.RawRecovery.Nearest.singleExposureEnvelope, ResourcePool.count_add,
    Recovery.Parameters.nearestPreparation_count_zero event outside modulus preparation]
  omega

private lemma nearestEnvelope_quantum_weight_zero {model : ExecutionModel}
    [BitWord.Selected model] {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth) :
    ResourcePool.weightedCount Resource.Event.quantumDuration
      (EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope model curve modulus) = 0 := by
  classical
  apply ResourcePool.weightedCount_eq_zero_of_mem
  intro event present
  by_cases operation : ∃ label, event = .classicalOperation label
  · obtain ⟨label, rfl⟩ := operation
    rfl
  · have zero := nearestEnvelope_count_zero curve modulus event
      (by intro label same; exact operation ⟨label, same⟩)
    exact False.elim ((Multiset.count_eq_zero.mp zero) present)

private lemma count_three {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {middle next final : RuntimeCtx model.kind}
    (first : Circuit model ctx middle) (second : Circuit model middle next)
    (third : Circuit model next final) (event : Resource.Event model)
    (path : ((first.seq second).seq third).Path) :
    ResourcePool.count event (((first.seq second).seq third).resourcePool path) =
      ResourcePool.count event (first.resourcePool path.1.1) +
        ResourcePool.count event (second.resourcePool path.1.2) +
          ResourcePool.count event (third.resourcePool path.2) := by
  rw [Recovery.Parameters.sequential_pool, ResourcePool.count_add,
    Recovery.Parameters.sequential_pool, ResourcePool.count_add]

private lemma weight_three {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    {middle next final : RuntimeCtx model.kind}
    (first : Circuit model ctx middle) (second : Circuit model middle next)
    (third : Circuit model next final) (weight : Resource.Event model → Nat)
    (path : ((first.seq second).seq third).Path) :
    ResourcePool.weightedCount weight (((first.seq second).seq third).resourcePool path) =
      ResourcePool.weightedCount weight (first.resourcePool path.1.1) +
        ResourcePool.weightedCount weight (second.resourcePool path.1.2) +
          ResourcePool.weightedCount weight (third.resourcePool path.2) := by
  rw [Recovery.Parameters.sequential_pool, ResourcePool.weightedCount_add,
    Recovery.Parameters.sequential_pool, ResourcePool.weightedCount_add]

private lemma count_zero_of_envelope {model : ExecutionModel} (event : Resource.Event model)
    (actual budget : ResourcePool model) (bounded : actual ≤ budget)
    (zero : ResourcePool.count event budget = 0) : ResourcePool.count event actual = 0 := by
  have counted := (ResourcePool.le_iff_count.mp bounded) event
  rw [zero] at counted
  exact Nat.eq_zero_of_le_zero counted

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel} (original : Inputs ctx)

private def resetParameters (output : CWriteRef ctx (.finite 2)) : Cleanup.Parameters ctx :=
  ⟨original.sameWires, output⟩

attribute [local irreducible] Initialization.program Initialization.placedProgram

private lemma restart_pool (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    (original.restart (services := services) output).resourcePool path =
      ((original.resetParameters output).prepared (services := services)
        (Initialization.placedProgram (ctx := ctx) (original.resetParameters output)
          original.seedX original.seedY)).resourcePool path := by
  unfold restart at path ⊢
  unfold resetParameters
  rfl

/-- Every original reset and actual fixed loader is paid before the sampler. -/
lemma restart_native_le (output : CWriteRef ctx (.finite 2))
    (coordinate : AlgorithmGate.Coordinate)
    (path : (original.restart (services := services) output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) ((original.restart (services := services) output).resourcePool path) ≤
        if coordinate = .singleQubit then 1366 else 0 := by
  have actual := Initialization.prepared_native_counts
    (services := services) (original.resetParameters output)
    original.seedX original.seedY path
  have mapped := congrArg
    (fun pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) =>
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.gate coordinate) pool) (original.restart_pool output path)
  refine mapped.le.trans ?_
  cases coordinate with
  | toffoli => exact actual.1.le
  | cnot => exact actual.2.1.le
  | singleQubit => exact actual.2.2

/-- The real whole-bank restart contains all 854 physical measurements. -/
lemma restart_measurement_count (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) ((original.restart (services := services) output).resourcePool path) =
        854 := by
  have actual := Initialization.prepared_measurement_count
    (services := services) (original.resetParameters output)
    original.seedX original.seedY path
  exact (congrArg
    (fun pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) =>
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        (.measurement (2 : ℕ+)) pool)
    (original.restart_pool output path)).trans actual

/-- The existing physical reset and native fixed loader keep their actual depth bound. -/
lemma restart_quantumTime_le (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    (original.restart (services := services) output).depth Resource.Event.quantumDuration path ≤ 855
      := by
  have actual := Initialization.prepared_quantumTime_le
    (services := services) (original.resetParameters output)
    original.seedX original.seedY path
  have embedded : (original.restart (services := services) output).depth
    Resource.Event.quantumDuration path =
      ((original.resetParameters output).prepared (services := services)
        (Initialization.placedProgram (ctx := ctx) (original.resetParameters output)
          original.seedX original.seedY)).depth Resource.Event.quantumDuration path :=
    by
      unfold restart at path ⊢
      unfold resetParameters
      rfl
  exact embedded.le.trans actual

/-- Physical reset and the same X loader emit no native classical instruction. -/
lemma restart_classical_weight (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.restart (services := services) output).resourcePool path) = 0 := by
  have actual := Initialization.prepared_classical_weight
    (services := services) (original.resetParameters output)
    original.seedX original.seedY path
  exact (congrArg
    (fun pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) =>
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool)
    (original.restart_pool output path)).trans actual

private lemma sampler_resident_le (sampler : Sampling.Parameters ctx)
    (path : (Sampling.circuit (services := services) sampler).Path) :
    (Sampling.circuit (services := services) sampler).peakResidentSpace path ≤
      Recovery.Parameters.samplerAdditionalSpace + ctx.residentSpace :=
  Recovery.Parameters.sequence_resident_le sampler schedule path

private lemma sampler_auxiliary_le (sampler : Sampling.Parameters ctx)
    (path : (Sampling.circuit (services := services) sampler).Path) :
    (Sampling.circuit (services := services) sampler).peakAuxiliarySpace path ≤
      Recovery.Parameters.samplerAdditionalSpace + ctx.auxiliarySpace :=
  Recovery.Parameters.sequence_auxiliary_le sampler schedule path

attribute [local irreducible] restart Sampling.circuit
  EllipticCurve.CandidateCheck.Native.Nearest.attemptInto
  EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope
  Circuit.resourcePool Circuit.depth

/-- The actual three serial groups preserve their separately proved native event allowances. -/
lemma attempt_native_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      coordinate)
      ((original.attempt (services := services) sampler checkers).resourcePool path) ≤
      Recovery.Parameters.sampleNativeLimit coordinate := by
  unfold attempt at path ⊢
  have reset := original.restart_native_le (sampler.output 0) coordinate path.1.1
  have sample := sampler.circuit_native_count_le (services := services) coordinate path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  have zero := count_zero_of_envelope (model := .quantum AlgorithmGate.model .empty BitWord.model
    services) (.gate coordinate) _ _ checked
    (nearestEnvelope_count_zero (model := .quantum AlgorithmGate.model .empty BitWord.model
      services) original.curve original.order (.gate coordinate)
      (by intro label same; cases same))
  rw [count_three, zero, Nat.add_zero]
  exact (Nat.add_le_add reset sample).trans_eq (Nat.add_comm _ _)

/-- One real attempt includes both the sampler measurements and the full physical restart. -/
lemma attempt_measurement_count (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((original.attempt (services := services) sampler checkers).resourcePool path) = 71526 := by
  unfold attempt at path ⊢
  have reset := original.restart_measurement_count (services := services) (sampler.output 0)
    path.1.1
  have sample := sampler.circuit_measurement_count (services := services) path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  have zero := count_zero_of_envelope (model := .quantum AlgorithmGate.model .empty BitWord.model
    services) (.measurement (2 : ℕ+)) _ _ checked
    (nearestEnvelope_count_zero (model := .quantum AlgorithmGate.model .empty BitWord.model
      services) original.curve original.order (.measurement (2 : ℕ+))
      (by intro label same; cases same))
  rw [count_three, reset, sample, zero]

/-- The paid nearest checker contributes no quantum duration to the same actual attempt. -/
lemma attempt_quantumTime_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    (original.attempt (services := services) sampler checkers).depth Resource.Event.quantumDuration
      path ≤
      57061815979 := by
  unfold attempt at path ⊢
  have reset := original.restart_quantumTime_le (services := services) (sampler.output 0) path.1.1
  have sample := sampler.circuit_quantumTime_le (services := services) path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  have checkedDepth := Circuit.depth_le_weightedCount_of_pool_le
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptInto (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) original.curve original.order
      (Recovery.pairedInput sampler) original.base original.target checkers.inverseSuccess
      checkers.candidate checkers.reconstruction checkers.scalarResult checkers.targetAccepted
      checkers.accepted checkers.selected) Resource.Event.quantumDuration _ path.2 checked
  rw [nearestEnvelope_quantum_weight_zero] at checkedDepth
  have zero := Nat.eq_zero_of_le_zero checkedDepth
  rw [Recovery.Parameters.sequential_depth, Recovery.Parameters.sequential_depth,
    zero, Nat.add_zero]
  exact Nat.add_le_add reset sample

/-- Native classical work includes the actual table builder and the explicit original checker. -/
lemma attempt_classical_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.attempt (services := services) sampler checkers).resourcePool path) ≤ 6762727521 :=
        by
  unfold attempt at path ⊢
  have reset := original.restart_classical_weight (services := services) (sampler.output 0) path.1.1
  have sample := Recovery.Parameters.sampler_classical_le (services := services) sampler path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_pool_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  have budget := (Recovery.Parameters.classical_weight_le_card
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptEnvelope (.quantum AlgorithmGate.model
      .empty BitWord.model services) original.curve
      original.order)).trans
        (Recovery.Parameters.nearestChecker_card_le (.quantum AlgorithmGate.model .empty
          BitWord.model services) original.curve original.order)
  have checker := (ResourcePool.weightedCount_mono
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      Resource.Event.classicalOperationWeight checked).trans budget
  rw [weight_three, reset, Nat.zero_add]
  exact Nat.add_le_add sample checker


attribute [local irreducible] scopedAttempts withFrame

/-- Each attempted native event remains bounded through the single actual feedback scope. -/
lemma scopedAttempts_native_le (count : Nat) (coordinate : AlgorithmGate.Coordinate)
    (path : (original.scopedAttempts (services := services) count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      coordinate)
      ((original.scopedAttempts (services := services) count).resourcePool path) ≤
        count * Recovery.Parameters.sampleNativeLimit coordinate := by
  unfold scopedAttempts at path ⊢
  apply withFrame_count_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ (.gate coordinate)
    (count * Recovery.Parameters.sampleNativeLimit coordinate) ?_ path
  intro inner transport same frame fresh selected
  exact Recovery.Parameters.repeated_count_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      _ (.gate coordinate) _
    (fun current => attempt_native_le (services := services) _ _ _ coordinate current) count
      selected

/-- Every original physical measurement survives allocation and release of feedback cells. -/
lemma scopedAttempts_measurement_count (count : Nat)
    (path : (original.scopedAttempts (services := services) count).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((original.scopedAttempts (services := services) count).resourcePool path) = count * 71526 :=
        by
  unfold scopedAttempts at path ⊢
  apply withFrame_event_count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    _ 256 256 _ (.measurement (2 : ℕ+)) (count * 71526) ?_ path
  intro inner transport same frame fresh selected
  exact Circuit.forRange_event_count
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) count _ 71526
    (fun _ current => attempt_measurement_count (services := services) _ _ _ current) selected

/-- The real loop preserves the same-path duration allowance without charging classical work. -/
lemma scopedAttempts_quantumTime_le (count : Nat)
    (path : (original.scopedAttempts (services := services) count).Path) :
    (original.scopedAttempts (services := services) count).depth Resource.Event.quantumDuration path
      ≤
      count * 57061815979 := by
  unfold scopedAttempts at path ⊢
  apply withFrame_depth_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ Resource.Event.quantumDuration
    (count * 57061815979) ?_ path
  intro inner transport same frame fresh selected
  exact Recovery.Parameters.repeated_depth_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      _ Resource.Event.quantumDuration _
    (fun current => attempt_quantumTime_le (services := services) _ _ _ current) count selected

/-- Actual table construction, nearest recovery, checking and latching remain paid each time. -/
lemma scopedAttempts_classical_le (count : Nat)
    (path : (original.scopedAttempts (services := services) count).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.scopedAttempts (services := services) count).resourcePool path) ≤ count *
        6762727521 := by
  unfold scopedAttempts at path ⊢
  apply withFrame_weightedCount_le (model := .quantum AlgorithmGate.model .empty BitWord.model
    services) _ 256 256 _ Resource.Event.classicalOperationWeight
    (count * 6762727521) ?_ path
  intro inner transport same frame fresh selected
  exact Recovery.Parameters.repeated_weight_upper
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      _ Resource.Event.classicalOperationWeight _
    (fun current => attempt_classical_le (services := services) _ _ _ current) count selected


/-- The original seven destinations are retained once; the final pack emits no quantum gate. -/
lemma run_native_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services) (.gate
      coordinate)
      ((original.run (services := services)).code.resourcePool path) ≤
        Recovery.Parameters.runNativeLimit coordinate := by
  unfold run at path ⊢
  have repeated := original.scopedAttempts_native_le (services := services) 3 coordinate path.1.2
  have packed := Recovery.Parameters.pack_nonclassical_zero (services := services)
    (.gate coordinate) (by intro label same; cases same) path.2
  rw [count_three, EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.count_zero, packed, Nat.zero_add, Nat.add_zero]
  exact repeated

/-- All 102 drivers and all three physical restarts are counted on the real factory path. -/
lemma run_measurement_count (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+))
      ((original.run (services := services)).code.resourcePool path) = 214578 := by
  unfold run at path ⊢
  have repeated := original.scopedAttempts_measurement_count (services := services) 3 path.1.2
  have packed := Recovery.Parameters.pack_nonclassical_zero (services := services)
    (.measurement (2 : ℕ+)) (by intro label same; cases same) path.2
  rw [count_three, EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.count_zero, packed, Nat.zero_add, Nat.add_zero]
  exact repeated

/-- The actual fresh-scratch factory keeps the independently derived quantum duration cap. -/
lemma run_quantumTime_le (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.depth Resource.Event.quantumDuration path ≤
      171185447937 := by
  unfold run at path ⊢
  have repeated := original.scopedAttempts_quantumTime_le (services := services) 3 path.1.2
  have retained := EllipticCurve.CandidateCheck.Native.retainPersistent_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
      Resource.Event.quantumDuration path.1.1
  have packed := EllipticCurve.CandidateCheck.Native.packBatchResult_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
      Resource.Event.quantumDuration path.2
  have packedZero : _ = (0 : Nat) := packed.trans rfl
  have outer := Recovery.Parameters.sequential_depth
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    ((EllipticCurve.CandidateCheck.Native.retainPersistent (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260).seq
      (original.scopedAttempts (services := services) 3))
    (EllipticCurve.CandidateCheck.Native.packBatchResult (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260)
    Resource.Event.quantumDuration path
  have inner := Recovery.Parameters.sequential_depth
    (EllipticCurve.CandidateCheck.Native.retainPersistent (model := .quantum AlgorithmGate.model
      .empty BitWord.model services) ctx 256 260)
    (original.scopedAttempts (services := services) 3) Resource.Event.quantumDuration path.1
  rw [inner, retained, packedZero, Nat.zero_add, Nat.add_zero] at outer
  exact outer.le.trans repeated

/-- The final option pack is paid after the feedback scope has exited. -/
lemma run_classical_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((original.run (services := services)).code.resourcePool path) ≤ 20288182564 := by
  unfold run at path ⊢
  have repeated := original.scopedAttempts_classical_le (services := services) 3 path.1.2
  have packed : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((EllipticCurve.CandidateCheck.Native.packBatchResult (model := .quantum AlgorithmGate.model
        .empty BitWord.model services)
        ctx 256 260).resourcePool path.2) = 1 := by
    rw [EllipticCurve.CandidateCheck.Native.packBatchResult_resourcePool]
    rfl
  rw [weight_three, EllipticCurve.CandidateCheck.Native.retainPersistent_resourcePool,
    ResourcePool.weightedCount_zero, packed, Nat.zero_add]
  exact Nat.add_le_add_right repeated 1


/-- The sampler and explicit checker reuse successive scratch scopes in one feedback frame. -/
def attemptAdditionalSpace : SpacePool .quantum :=
  SpacePool.max Recovery.Parameters.samplerAdditionalSpace
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260)

/-- Feedback is released before the actual optional result is retained. -/
def runAdditionalSpace : SpacePool .quantum :=
  SpacePool.max (frameSpace .quantum 256 256 + attemptAdditionalSpace)
    (SpacePool.ofShape (.option (.unsignedWord 260)))

private lemma sampler_extra_le :
    Recovery.Parameters.samplerAdditionalSpace ≤ attemptAdditionalSpace :=
  SpacePool.le_max_left _ _

private lemma checker_extra_le :
    EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260 ≤
      attemptAdditionalSpace := SpacePool.le_max_right _ _

private lemma frame_extra_le :
    frameSpace .quantum 256 256 + attemptAdditionalSpace ≤ runAdditionalSpace :=
  SpacePool.le_max_left _ _

private lemma output_extra_le :
    SpacePool.ofShape (.option (.unsignedWord 260)) ≤ runAdditionalSpace :=
  SpacePool.le_max_right _ _

attribute [local irreducible] attemptAdditionalSpace runAdditionalSpace
  Circuit.peakResidentSpace Circuit.peakAuxiliarySpace

/-- The actual fixed loader preserves the complete original resident pool. -/
private lemma restart_resident (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    (original.restart (services := services) output).peakResidentSpace path = ctx.residentSpace :=
      by
  unfold restart at path ⊢
  exact Circuit.peakResidentSpace_embed
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (allowAllocation := true)
    (ContextEmbedding.identity ctx)
    (({ sameWires := original.sameWires, output := output } : Cleanup.Parameters ctx).prepared
      (services := services)
      (Initialization.placedProgram (ctx := ctx)
        ({ sameWires := original.sameWires, output := output } : Cleanup.Parameters ctx)
        original.seedX original.seedY)) path

/-- Actual reset, table builder, sampler and explicit checker retain all original resident roles. -/
lemma attempt_resident_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    (original.attempt (services := services) sampler checkers).peakResidentSpace path ≤
      attemptAdditionalSpace + ctx.residentSpace := by
  unfold attempt at path ⊢
  have reset := original.restart_resident (services := services) (sampler.output 0) path.1.1
  have sampled := sampler_resident_le (services := services) sampler path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_resident_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact reset.le.trans (le_add_of_nonneg_left zero_le)
    · exact sampled.trans (add_le_add sampler_extra_le le_rfl)
  · exact checked.trans (add_le_add checker_extra_le le_rfl)

/-- The actual single feedback scope charges every fresh cell beside repeated body scratch. -/
lemma scopedAttempts_resident_le (count : Nat)
    (path : (original.scopedAttempts (services := services) count).Path) :
    (original.scopedAttempts (services := services) count).peakResidentSpace path ≤
      frameSpace .quantum 256 256 + attemptAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
  unfold Circuit.peakResidentSpace
  unfold scopedAttempts at path ⊢
  apply withFrame_peak_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ RuntimeCtx.residentSpace
    RuntimeCtx.residentSpace_addWorkspace attemptAdditionalSpace ?_ path
  intro inner transport same frame fresh selected
  simpa only [Circuit.peakResidentSpace] using
    (Circuit.forRange_resident_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) count _
    (attemptAdditionalSpace + (show SpacePool .quantum from inner.residentSpace))
    (le_add_of_nonneg_left zero_le)
    (fun _ current => attempt_resident_le (services := services) _ _ _ current) selected)

/-- Original caller storage, seven retained destinations and the real feedback lifetime are kept. -/
lemma run_resident_le (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakResidentSpace path ≤ runAdditionalSpace +
      EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
        ctx.residentSpace := by
  have repeated := (original.scopedAttempts_resident_le (services := services) 3 path.1.2).trans
    (add_le_add frame_extra_le le_rfl)
  have actual : (original.run (services := services)).code.peakResidentSpace path ≤
    runAdditionalSpace
    +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.2).le.trans (add_le_add output_extra_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_residentSpace, add_assoc]
    using actual

/-- The actual fixed loader preserves the complete original auxiliary pool. -/
private lemma restart_auxiliary (output : CWriteRef ctx (.finite 2))
    (path : (original.restart (services := services) output).Path) :
    (original.restart (services := services) output).peakAuxiliarySpace path = ctx.auxiliarySpace :=
      by
  unfold restart at path ⊢
  exact Circuit.peakAuxiliarySpace_embed
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (allowAllocation := true)
    (ContextEmbedding.identity ctx)
    (({ sameWires := original.sameWires, output := output } : Cleanup.Parameters ctx).prepared
      (services := services)
      (Initialization.placedProgram (ctx := ctx)
        ({ sameWires := original.sameWires, output := output } : Cleanup.Parameters ctx)
        original.seedX original.seedY)) path

/-- Reset, table builder, sampler and explicit checker keep all auxiliary roles. -/
lemma attempt_auxiliary_le (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (path : (original.attempt (services := services) sampler checkers).Path) :
    (original.attempt (services := services) sampler checkers).peakAuxiliarySpace path ≤
      attemptAdditionalSpace + ctx.auxiliarySpace := by
  unfold attempt at path ⊢
  have reset := original.restart_auxiliary (services := services) (sampler.output 0) path.1.1
  have sampled := sampler_auxiliary_le (services := services) sampler path.1.2
  have checked := EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_auxiliary_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) original.curve
      original.order (Recovery.pairedInput sampler)
    original.base original.target checkers.inverseSuccess checkers.candidate checkers.reconstruction
    checkers.scalarResult checkers.targetAccepted checkers.accepted checkers.selected path.2
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
    · exact reset.le.trans (le_add_of_nonneg_left zero_le)
    · exact sampled.trans (add_le_add sampler_extra_le le_rfl)
  · exact checked.trans (add_le_add checker_extra_le le_rfl)

/-- The actual single feedback scope charges every fresh cell beside repeated body scratch. -/
lemma scopedAttempts_auxiliary_le (count : Nat)
    (path : (original.scopedAttempts (services := services) count).Path) :
    (original.scopedAttempts (services := services) count).peakAuxiliarySpace path ≤
      frameSpace .quantum 256 256 + attemptAdditionalSpace +
        (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
  unfold Circuit.peakAuxiliarySpace
  unfold scopedAttempts at path ⊢
  apply withFrame_peak_le (model := .quantum AlgorithmGate.model .empty BitWord.model services) _
    256 256 _ RuntimeCtx.auxiliarySpace
    RuntimeCtx.auxiliarySpace_addWorkspace attemptAdditionalSpace ?_ path
  intro inner transport same frame fresh selected
  simpa only [Circuit.peakAuxiliarySpace] using
    (Circuit.forRange_auxiliary_le
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) count _
    (attemptAdditionalSpace + (show SpacePool .quantum from inner.auxiliarySpace))
    (le_add_of_nonneg_left zero_le)
    (fun _ current => attempt_auxiliary_le (services := services) _ _ _ current) selected)

/-- Original caller storage, seven retained destinations and the real feedback lifetime are kept. -/
lemma run_auxiliary_le (path : (original.run (services := services)).code.Path) :
    (original.run (services := services)).code.peakAuxiliarySpace path ≤ runAdditionalSpace +
      EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
        ctx.auxiliarySpace := by
  have repeated := (original.scopedAttempts_auxiliary_le (services := services) 3 path.1.2).trans
    (add_le_add frame_extra_le le_rfl)
  have actual : (original.run (services := services)).code.peakAuxiliarySpace path ≤
    runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
          path.2).le.trans (add_le_add output_extra_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_auxiliarySpace, add_assoc]
    using actual

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
