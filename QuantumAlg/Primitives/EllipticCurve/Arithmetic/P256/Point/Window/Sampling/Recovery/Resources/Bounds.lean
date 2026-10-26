/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Resources
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Resources.Bounds
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Initialization.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Budget.Values
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Resources.Space

/-!
# Actual three-round native resources, restart and paid checked recovery

All 102 complete point/table drivers, 1560 window positions, three complete
854-system restarts and their native fixed loaders are charged. The original
nearest decoder, candidate checking and final option pack remain separate
native classical work. Quantum time follows the actual sequential syntax.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution ClassicalRoutines

namespace Recovery.Parameters

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Recovery.Parameters ctx)

def sampleNativeLimit (coordinate : AlgorithmGate.Coordinate) : Nat :=
  samplerNativeLimit coordinate + if coordinate = .singleQubit then 1366 else 0

def runNativeLimit (coordinate : AlgorithmGate.Coordinate) : Nat :=
  3 * sampleNativeLimit coordinate

def runQuantumTimeLimit : Nat := 171185447937

/-- Actual builder and six runtime-query classical work, including both paid mask packs. -/
def windowClassicalLimit (index : WindowIndex) : Nat :=
  if index.full then 210807225 else 105477

def samplerClassicalLimit : Nat := 6746042154

/-- The five largest live arrays coexist with the actual classical builder scratch. -/
def samplerAdditionalSpace : SpacePool .quantum :=
  EllipticCurve.WindowTables.Outer.tableSpace .quantum 256 (2 ^ 16) +
    EllipticCurve.WindowTables.Outer.coefficientScratchSpace .quantum 256

/-- Successive table/checker scopes share a maximum beside the retained original caller. -/
def runAdditionalSpace : SpacePool .quantum :=
  SpacePool.max
    (SpacePool.max samplerAdditionalSpace
      (EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260))
    (SpacePool.ofShape (.option (.unsignedWord 260)))

attribute [local irreducible] Circuit.peakResidentSpace Circuit.peakAuxiliarySpace
  EllipticCurve.WindowTables.Outer.coefficientScratchSpace

private lemma sequential_weight {model : ExecutionModel}
    {pre mid post : RuntimeCtx model.kind} {allocation : Bool}
    (first : Circuit model pre mid allocation) (second : Circuit model mid post allocation)
    (weight : Resource.Event model → Nat) (path : (first.seq second).Path) :
    ResourcePool.weightedCount weight ((first.seq second).resourcePool path) =
      ResourcePool.weightedCount weight (first.resourcePool path.1) +
        ResourcePool.weightedCount weight (second.resourcePool path.2) := by
  change ResourcePool.weightedCount weight
    (ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
  rfl

private lemma driver_space_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (index : WindowIndex) :
    (parameters.pointParameters index).additionalSpace ≤ samplerAdditionalSpace := by
  have tables : EllipticCurve.WindowTables.Outer.tableSpace .quantum 256
      (2 ^ (index.highRemaining + index.lowWidth + 1)) ≤
        EllipticCurve.WindowTables.Outer.tableSpace .quantum 256 (2 ^ 16) := by
    intro axis
    cases axis with
    | classicalBits =>
        rw [EllipticCurve.WindowTables.Outer.tableSpace_classicalBits,
          EllipticCurve.WindowTables.Outer.tableSpace_classicalBits]
        by_cases full : index.full <;>
          norm_num [WindowIndex.highRemaining, WindowIndex.lowWidth, full]
    | quantumSystems dimension =>
        rw [EllipticCurve.WindowTables.Outer.tableSpace_quantumSystems,
          EllipticCurve.WindowTables.Outer.tableSpace_quantumSystems]
  exact add_le_add tables (le_rfl :
    EllipticCurve.WindowTables.Outer.coefficientScratchSpace .quantum 256 ≤
      EllipticCurve.WindowTables.Outer.coefficientScratchSpace .quantum 256)

private lemma sampler_space_le : samplerAdditionalSpace ≤ runAdditionalSpace :=
  (SpacePool.le_max_left samplerAdditionalSpace
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260)).trans
      (SpacePool.le_max_left _ (SpacePool.ofShape (.option (.unsignedWord 260))))

private lemma checker_space_le :
    EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260 ≤
      runAdditionalSpace :=
  (SpacePool.le_max_right samplerAdditionalSpace
    (EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace .quantum 256 260)).trans
      (SpacePool.le_max_left _ (SpacePool.ofShape (.option (.unsignedWord 260))))

private lemma output_space_le :
    SpacePool.ofShape (.option (.unsignedWord 260)) ≤ runAdditionalSpace :=
  SpacePool.le_max_right _ _

private lemma persistentChecker_resident_le {model : ExecutionModel} [BitWord.Selected model]
    {caller : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef caller (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef caller (EllipticCurve.PointShape width))
    (path : (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).Path) :
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).peakResidentSpace path ≤
        EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace model.kind width
          scalarWidth +
          (EllipticCurve.CandidateCheck.Native.persistentCtx caller width
            scalarWidth).residentSpace := by
  exact EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_resident_le
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


private lemma persistentChecker_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    {caller : RuntimeCtx model.kind} {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef caller (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef caller (EllipticCurve.PointShape width))
    (path : (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).Path) :
    (EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt
      (model := model) curve modulus sample base target).peakAuxiliarySpace path ≤
        EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace model.kind width
          scalarWidth +
          (EllipticCurve.CandidateCheck.Native.persistentCtx caller width
            scalarWidth).auxiliarySpace := by
  exact EllipticCurve.CandidateCheck.Native.Nearest.attemptInto_auxiliary_le
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


attribute [local irreducible] samplerAdditionalSpace runAdditionalSpace
  EllipticCurve.CandidateCheck.Native.Nearest.attemptScratchSpace
  EllipticCurve.CandidateCheck.Native.Nearest.persistentAttempt

private lemma block_resident_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).peakResidentSpace path ≤
      samplerAdditionalSpace + inner.residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le ?_ ?_)
  · exact (Circuit.peakResidentSpace_embed (allowAllocation := true)
      (ContextEmbedding.identity inner)
      (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index))
      path.1).le.trans (le_add_of_nonneg_left zero_le)
  · refine (Circuit.peakResidentSpace_seq _ _ path.2).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact (Circuit.peakResidentSpace_unitary (allowAllocation := true)
        (operations := BitWord.model) (classicalOracles := services)
        (QuantumFourierTransform.Semiclassical.Window.preparation
          (index.lowerWidth + 1) (parameters.ports index)) path.2.1).le.trans
            (le_add_of_nonneg_left zero_le)
    · refine (Circuit.peakResidentSpace_seq _ _ path.2.2).le.trans
        (SpacePool.max_le ?_ ?_)
      · exact ((parameters.pointParameters index).circuit_resident_le parameters.frame
          parameters.modulus index.row path.2.2.1).trans
            (add_le_add (driver_space_le parameters index) le_rfl)
      · exact (Circuit.peakResidentSpace_embed (allowAllocation := true)
          (ContextEmbedding.identity inner)
          (QuantumFourierTransform.Semiclassical.Window.inverseCode
            (operations := BitWord.model) (services := services) (parameters.ports index))
          path.2.2.2).le.trans (le_add_of_nonneg_left zero_le)

private lemma block_auxiliary_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (index : WindowIndex)
    (path : (parameters.block (services := services) index).Path) :
    (parameters.block index).peakAuxiliarySpace path ≤
      samplerAdditionalSpace + inner.auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le ?_ ?_)
  · exact (Circuit.peakAuxiliarySpace_embed (allowAllocation := true)
      (ContextEmbedding.identity inner)
      (parameters.resetParameters.run (index.lowerWidth + 1) (parameters.wire index))
      path.1).le.trans (le_add_of_nonneg_left zero_le)
  · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2).le.trans
      (SpacePool.max_le ?_ ?_)
    · exact (Circuit.peakAuxiliarySpace_unitary (allowAllocation := true)
        (operations := BitWord.model) (classicalOracles := services)
        (QuantumFourierTransform.Semiclassical.Window.preparation
          (index.lowerWidth + 1) (parameters.ports index)) path.2.1).le.trans
            (le_add_of_nonneg_left zero_le)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.2.2).le.trans
        (SpacePool.max_le ?_ ?_)
      · exact ((parameters.pointParameters index).circuit_auxiliary_le parameters.frame
          parameters.modulus index.row path.2.2.1).trans
            (add_le_add (driver_space_le parameters index) le_rfl)
      · exact (Circuit.peakAuxiliarySpace_embed (allowAllocation := true)
          (ContextEmbedding.identity inner)
          (QuantumFourierTransform.Semiclassical.Window.inverseCode
            (operations := BitWord.model) (services := services) (parameters.ports index))
          path.2.2.2).le.trans (le_add_of_nonneg_left zero_le)

private lemma sequence_resident_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    (parameters.sequence indices).peakResidentSpace path ≤
      samplerAdditionalSpace + inner.residentSpace := by
  induction indices with
  | nil =>
      exact (Circuit.peakResidentSpace_id path).le.trans (le_add_of_nonneg_left zero_le)
  | cons index rest ih =>
      exact (Circuit.peakResidentSpace_seq _ _ path).le.trans
        (SpacePool.max_le (block_resident_le parameters index path.1) (ih path.2))

private lemma sequence_auxiliary_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (indices : List WindowIndex)
    (path : (parameters.sequence (services := services) indices).Path) :
    (parameters.sequence indices).peakAuxiliarySpace path ≤
      samplerAdditionalSpace + inner.auxiliarySpace := by
  induction indices with
  | nil =>
      exact (Circuit.peakAuxiliarySpace_id path).le.trans (le_add_of_nonneg_left zero_le)
  | cons index rest ih =>
      exact (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
        (SpacePool.max_le (block_auxiliary_le parameters index path.1) (ih path.2))

private lemma sample_resident_le (path : (original.sample (services := services)).Path) :
    original.sample.peakResidentSpace path ≤ samplerAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans
    (SpacePool.max_le ?_ (sequence_resident_le original.samplerParameters schedule path.2))
  exact (Circuit.peakResidentSpace_embed (allowAllocation := true)
    (ContextEmbedding.identity _)
    (original.cleanupParameters.prepared
      (Initialization.placedProgram original.cleanupParameters original.seedX original.seedY))
    path.1).le.trans (le_add_of_nonneg_left zero_le)

private lemma sample_auxiliary_le (path : (original.sample (services := services)).Path) :
    original.sample.peakAuxiliarySpace path ≤ samplerAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans
    (SpacePool.max_le ?_ (sequence_auxiliary_le original.samplerParameters schedule path.2))
  exact (Circuit.peakAuxiliarySpace_embed (allowAllocation := true)
    (ContextEmbedding.identity _)
    (original.cleanupParameters.prepared
      (Initialization.placedProgram original.cleanupParameters original.seedX original.seedY))
    path.1).le.trans (le_add_of_nonneg_left zero_le)

private lemma attempt_resident_le (path : (original.attempt (services := services)).Path) :
    original.attempt.peakResidentSpace path ≤ runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (original.sample_resident_le path.1).trans
      (add_le_add sampler_space_le le_rfl)
  · have actual := @persistentChecker_resident_le
      (.quantum AlgorithmGate.model .empty BitWord.model services)
      (BitWord.selectedQuantum AlgorithmGate.model .empty services) ctx 256 260
      original.curve original.order (Recovery.pairedInput original.sampler)
      original.base original.target path.2
    exact actual.trans (add_le_add checker_space_le le_rfl)

private lemma attempt_auxiliary_le (path : (original.attempt (services := services)).Path) :
    original.attempt.peakAuxiliarySpace path ≤ runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact (original.sample_auxiliary_le path.1).trans
      (add_le_add sampler_space_le le_rfl)
  · have actual := @persistentChecker_auxiliary_le
      (.quantum AlgorithmGate.model .empty BitWord.model services)
      (BitWord.selectedQuantum AlgorithmGate.model .empty services) ctx 256 260
      original.curve original.order (Recovery.pairedInput original.sampler)
      original.base original.target path.2
    exact actual.trans (add_le_add checker_space_le le_rfl)

/-- All original resident storage and all seven retained cells remain charged throughout. -/
lemma run_resident_le (path : (original.run (services := services)).code.Path) :
    original.run.code.peakResidentSpace path ≤ runAdditionalSpace +
      EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
        ctx.residentSpace := by
  have repeated := Circuit.forRange_resident_le 3 (fun _ => original.attempt)
    (runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace)
    (le_add_of_nonneg_left zero_le) (fun _ current => original.attempt_resident_le current)
    path.1.2
  have actual : original.run.code.peakResidentSpace path ≤ runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260 path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_resident
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260 path.2).le.trans
          (add_le_add output_space_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_residentSpace, add_assoc]
    using actual

/-- The same lexical maximum preserves every pre-existing auxiliary role. -/
lemma run_auxiliary_le (path : (original.run (services := services)).code.Path) :
    original.run.code.peakAuxiliarySpace path ≤ runAdditionalSpace +
      EllipticCurve.CandidateCheck.Native.persistentCellSpace .quantum 256 260 +
        ctx.auxiliarySpace := by
  have repeated := Circuit.forRange_auxiliary_le 3 (fun _ => original.attempt)
    (runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace)
    (le_add_of_nonneg_left zero_le) (fun _ current => original.attempt_auxiliary_le current)
    path.1.2
  have actual : original.run.code.peakAuxiliarySpace path ≤ runAdditionalSpace +
      (EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ repeated)
      exact (EllipticCurve.CandidateCheck.Native.retainPersistent_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260 path.1.1).le.trans (le_add_of_nonneg_left zero_le)
    · exact (EllipticCurve.CandidateCheck.Native.packBatchResult_auxiliary
        (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx 256 260 path.2).le.trans
          (add_le_add output_space_le le_rfl)
  simpa only [EllipticCurve.CandidateCheck.Native.persistentCtx_auxiliarySpace, add_assoc]
    using actual

lemma schedule_classical_limit_sum :
    (schedule.map windowClassicalLimit).sum = samplerClassicalLimit := by
  decide +kernel

private lemma actualClassicalLimit {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner) (index : WindowIndex) :
    (parameters.pointParameters index).classicalLimit = windowClassicalLimit index := by
  change EllipticCurve.WindowTables.TableFrame.constructionBudget
    256 (index.highRemaining + index.lowWidth + 1) +
      (6 * EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit
        256 index.highRemaining index.lowWidth + 2) = windowClassicalLimit index
  by_cases full : index.full <;>
    norm_num [WindowIndex.highRemaining, WindowIndex.lowWidth, windowClassicalLimit, full,
      EllipticCurve.WindowTables.TableFrame.constructionBudget_full16,
      EllipticCurve.WindowTables.TableFrame.constructionBudget_tail4,
      EncodedBit.WindowLookup.RuntimeTable.runtimeCycleClassicalLimit,
      EncodedBit.WindowLookup.staticCycleCnotLimit]

private lemma sampler_classical_le {inner : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters inner)
    (path : (Sampling.circuit (services := services) parameters).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Sampling.circuit parameters).resourcePool path) ≤ samplerClassicalLimit := by
  have actual := parameters.sequence_weight_le Resource.Event.classicalOperationWeight
    windowClassicalLimit (fun index current =>
      (parameters.block_classical_le index current).trans_eq
        (actualClassicalLimit parameters index)) schedule path
  rw [schedule_classical_limit_sum] at actual
  exact actual

lemma runNativeLimit_values :
    runNativeLimit .toffoli = 99272733288 ∧
      runNativeLimit .cnot = 81134896044 ∧
      runNativeLimit .singleQubit = 25700866770 := by
  have toffoli : AlgorithmGate.Coordinate.toffoli ≠ .singleQubit := by decide
  have cnot : AlgorithmGate.Coordinate.cnot ≠ .singleQubit := by decide
  norm_num [runNativeLimit, sampleNativeLimit, samplerNativeLimit, toffoli, cnot]

private lemma restart_native_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.restart (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) (original.restart.resourcePool path) ≤
        if coordinate = .singleQubit then 1366 else 0 := by
  have actual := Initialization.prepared_native_counts original.cleanupParameters
    original.seedX original.seedY path
  cases coordinate with
  | toffoli => exact actual.1.le
  | cnot => exact actual.2.1.le
  | singleQubit => exact actual.2.2

lemma sample_native_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.sample (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) (original.sample.resourcePool path) ≤ sampleNativeLimit coordinate := by
  have reset := original.restart_native_count_le coordinate path.1
  have sampled := original.samplerParameters.circuit_native_count_le coordinate path.2
  have split := Circuit.resourcePool_count_seq original.restart
    (Sampling.circuit original.samplerParameters)
    (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      coordinate) path
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.gate coordinate) (original.sample.resourcePool path) = _ at split
  rw [split]
  unfold sampleNativeLimit
  omega

/-- Every path executes the same three genuine samplers and every paid restart. -/
lemma run_native_count_le (coordinate : AlgorithmGate.Coordinate)
    (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.gate coordinate) (original.run.code.resourcePool path) ≤ runNativeLimit coordinate := by
  exact original.run_nonclassical_count_le (.gate coordinate)
    (by intro label incompatible; cases incompatible) (sampleNativeLimit coordinate)
    (fun current => original.sample_native_count_le coordinate current) path

lemma sample_measurement_count (path : (original.sample (services := services)).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) (original.sample.resourcePool path) = 71526 := by
  have reset := Initialization.prepared_measurement_count original.cleanupParameters
    original.seedX original.seedY path.1
  have sampled := original.samplerParameters.circuit_measurement_count path.2
  have split := Circuit.resourcePool_count_seq original.restart
    (Sampling.circuit original.samplerParameters)
    (Resource.Event.measurement
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) (2 : ℕ+)) path
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+)) (original.sample.resourcePool path) = _ at split
  rw [split]
  change ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (.measurement (2 : ℕ+))
    (original.restart.resourcePool path.1) = 854 at reset
  omega

/-- Exact MZ occurrence includes every window read/reset and every whole-bank restart. -/
lemma run_measurement_count (path : (original.run (services := services)).code.Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (.measurement (2 : ℕ+)) (original.run.code.resourcePool path) = 214578 := by
  exact original.run_nonclassical_count (.measurement (2 : ℕ+))
    (by intro label incompatible; cases incompatible) 71526
    (fun current => original.sample_measurement_count current) path

attribute [local irreducible] Circuit.depth

lemma sample_quantumTime_le (path : (original.sample (services := services)).Path) :
    original.sample.depth Resource.Event.quantumDuration path ≤ samplerQuantumTimeLimit + 855 := by
  have reset := Initialization.prepared_quantumTime_le original.cleanupParameters
    original.seedX original.seedY path.1
  have sampled := original.samplerParameters.circuit_quantumTime_le path.2
  have embedded : original.restart.depth Resource.Event.quantumDuration path.1 =
      (original.cleanupParameters.prepared
        (Initialization.placedProgram original.cleanupParameters original.seedX
          original.seedY)).depth
          Resource.Event.quantumDuration path.1 :=
    Circuit.quantumTime_embed (allowAllocation := true) (ContextEmbedding.identity _)
      (original.cleanupParameters.prepared
        (Initialization.placedProgram original.cleanupParameters original.seedX original.seedY))
      path.1
  exact (Circuit.depth_seq original.restart (Sampling.circuit original.samplerParameters)
    Resource.Event.quantumDuration path.1 path.2).le.trans
      ((Nat.add_le_add (embedded.le.trans reset) sampled).trans_eq
        (Nat.add_comm 855 samplerQuantumTimeLimit))

/-- Actual sequential dependency time is bounded independently of outcomes and old Stores. -/
lemma run_quantumTime_bound (path : (original.run (services := services)).code.Path) :
    original.run.code.depth Resource.Event.quantumDuration path ≤ runQuantumTimeLimit := by
  exact original.run_quantumTime_le (samplerQuantumTimeLimit + 855)
    (fun current => original.sample_quantumTime_le current) path

attribute [local irreducible] Circuit.resourcePool ResourcePool.weightedCount

lemma sample_classical_le (path : (original.sample (services := services)).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (original.sample.resourcePool path) ≤ samplerClassicalLimit := by
  have resetPool : original.restart.resourcePool path.1 =
      (original.cleanupParameters.prepared
        (Initialization.placedProgram original.cleanupParameters original.seedX
          original.seedY)).resourcePool path.1 :=
    Circuit.resourcePool_embed (allowAllocation := true) (ContextEmbedding.identity _)
      (original.cleanupParameters.prepared
        (Initialization.placedProgram original.cleanupParameters original.seedX original.seedY))
      path.1
  have resetWeight := congrArg
    (fun pool : ResourcePool (.quantum AlgorithmGate.model .empty BitWord.model services) =>
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight pool) resetPool
  have reset := resetWeight.trans (Initialization.prepared_classical_weight
    original.cleanupParameters original.seedX original.seedY path.1)
  have sampled := sampler_classical_le original.samplerParameters path.2
  exact (sequential_weight original.restart (Sampling.circuit original.samplerParameters)
    Resource.Event.classicalOperationWeight path).le.trans
      ((Nat.add_le_add reset.le sampled).trans_eq (Nat.zero_add samplerClassicalLimit))

/-- Nearest/check/latch and final pack remain paid native classical work in their own model. -/
lemma run_classical_le (path : (original.run (services := services)).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (original.run.code.resourcePool path) ≤
        20238126462 + 3 * ResourcePool.weightedCount
          (model := .quantum AlgorithmGate.model .empty BitWord.model services)
          Resource.Event.classicalOperationWeight (original.checkerBudget (services :=
            services)) + 1 := by
  have actual := original.run_weight_le Resource.Event.classicalOperationWeight
    samplerClassicalLimit (fun current => original.sample_classical_le current) path
  change _ ≤ 3 * (6746042154 + ResourcePool.weightedCount
    Resource.Event.classicalOperationWeight (original.checkerBudget (services := services))) + 1
      at actual
  omega

end Recovery.Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
