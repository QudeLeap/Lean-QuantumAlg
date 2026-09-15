/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Allocation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Correctness
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Preservation

/-!
# Actual caller-visible fixed-batch recovery

The real allocator initializes all eight workspace packages, executes shared
initialization and all 120 original pair recoveries, writes the caller result,
and releases the complete lexical workspace. Correctness and resource bounds
refer to that same full execution, including arbitrary external references.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedBatchRecoveryMachine

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original sampled parameter is the only caller-side numerical entry condition. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N)) (before : Store ctx)
    (parameter : CInputRef ctx (ParameterShape N)) : Prop where
  parameterValue : before.read parameter = Canonical.parameterValue input sample

/-- Exact original fixed-batch value of the sixteen caller terminal cells. -/
def batchValue {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N) (before : Store ctx) :
    CShape.Value (LatticeBatchRecoveryOutput.OutputShape N) :=
  LatticeBatchRecoveryOutput.outputValue
    (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N)
      (LatticePairRecoveryBatch.preparedSamples (preparedResidue sample) terminals before))

/-- Every original caller read outside the result cell survives the complete allocation. -/
def CallerFrame {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    result.key ∉ other.storageKeys → after.read other = before.read other

/-- The exact original output and complete caller frame belong to one actual final store. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (before after : Store ctx) : Prop where
  output : after.read (FirstAccepted.cellRead result) = batchValue sample terminals before
  callerFrame : CallerFrame result before after

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- References produced by the actual top and scratch allocators, with the lifted caller output. -/
def bodyRefs (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    {topCtx inner : RuntimeCtx kind}
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topTransport : Transport ctx topCtx)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (pairTransport : Transport topCtx inner) :
    LatticeBatchRecoveryWorkspaceBody.Refs ctx topCtx inner N where
  topTransport := topTransport
  pairTransport := pairTransport
  top := top
  cells := cells
  terminals := terminals
  parameter := parameter
  result := (topTransport.compose pairTransport).liftWrite result

/-- Allocate all original packages and execute the complete actual recovery body before release. -/
def into (ctx : RuntimeCtx kind) (input : Input N)
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) : Circuit ctx ctx :=
  LatticeBatchRecoveryWorkspace.withWorkspaces ctx N fun
    top _topDistinct topTransport _topSeparated cells pairTransport _certificates =>
      LatticeBatchRecoveryWorkspaceBody.into input
        (bodyRefs parameter terminals result top topTransport cells pairTransport)

private theorem bodyInitial {topCtx inner : RuntimeCtx kind} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (refs : LatticeBatchRecoveryWorkspaceBody.Refs ctx topCtx inner N) (before : Store inner)
    (parameterStored : before.read
      ((refs.topTransport.compose refs.pairTransport).liftInput refs.parameter) =
        Canonical.parameterValue input sample)
    (topInitialized : (transportCells refs.pairTransport refs.top).Initialized before) :
    LatticeBatchRecoveryWorkspaceBody.InitialConditions input sample refs before := by
  let _ : NeZero N := input.neZero
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨⟨sample, parameterStored⟩, ?_⟩
    change (before.read ((refs.topTransport.compose refs.pairTransport).liftInput
      refs.parameter)).first.toNat < N
    rw [parameterStored, parameterValue_unit_toNat input sample]
    exact ZMod.val_lt _
  · simpa only [LatticeBatchRecoveryWorkspaceViews.parameterAt,
      Transport.liftInput_compose] using parameterStored
  · have initialized := Cells.workspaceCells_cellAt_initialized
      (transportCells refs.pairTransport refs.top) before topInitialized
      (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N)
    have selector := LatticeBatchRecoveryWorkspaceViews.factorSelection_topAt
      refs.pairTransport refs.top
    change (before.read (FirstAccepted.cellRead
      (LatticeBatchRecoveryWorkspaceViews.foldRefs refs.topTransport refs.pairTransport refs.top
        refs.cells refs.terminals refs.parameter).factorSelection.accepted)).toBool = false
    change (before.read (FirstAccepted.cellRead
      (LatticePairFactorWorkspaceSeparation.liftSelection refs.pairTransport
        (LatticeBatchRecoveryWorkspaceLayout.factorSelection refs.top)).accepted)).toBool = false
    rw [← selector]
    exact congrArg CShape.Value.toBool initialized

private theorem bodyValue_restrict {topCtx inner : RuntimeCtx kind}
    (sample : Fin (2 ^ residueSamplingBits N))
    (refs : LatticeBatchRecoveryWorkspaceBody.Refs ctx topCtx inner N) (before : Store inner) :
    LatticeBatchRecoveryEndpoint.batchOutputValue sample
        (LatticeBatchRecoveryWorkspaceBody.endpointRefs refs) before =
      batchValue sample refs.terminals
        ((refs.topTransport.compose refs.pairTransport).restrict before) := by
  unfold LatticeBatchRecoveryEndpoint.batchOutputValue batchValue
  congr 2
  apply List.Vector.ext
  intro index
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map,
    List.Vector.get_ofFn]
  congr 1
  funext bit
  unfold BatchMachine.sourceBits
  change (before.read (.bitsGet (refs.pairTransport.liftInput
    (refs.topTransport.liftInput (refs.terminals index))) bit)).toBool = _
  rw [← Transport.liftInput_compose]
  exact congrArg CShape.Value.toBool
    ((refs.topTransport.compose refs.pairTransport).workspaceTransport_restrict_readsAs before
      (.bitsGet (refs.terminals index) bit))

private def Post (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (before after : Store ctx) : Prop :=
  CallerFrame result before after ∧
    ∀ sample, InitialConditions input sample before parameter →
      after.read (FirstAccepted.cellRead result) = batchValue sample terminals before

private theorem actualRecord_exists (input : Input N)
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) :
    ∃ record : Store ctx → Store ctx × (into ctx input parameter terminals result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (into ctx input parameter terminals result).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before, Post input parameter terminals result before (record before).1 := by
  unfold into
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_actualRecord_initialized_post
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
  let refs := bodyRefs parameter terminals result top topTransport cells pairTransport
  have separation : LatticeBatchRecoveryWorkspaceBody.Separation refs :=
    ⟨topDistinct, topSeparated, certificates⟩
  refine ⟨LatticeBatchRecoveryWorkspaceBody.step input refs,
    LatticeBatchRecoveryWorkspaceBody.into_execute input refs, ?_⟩
  intro before topInitialized _scratchInitialized
  have reads : (topTransport.compose pairTransport).ReadsAs
      ((topTransport.compose pairTransport).restrict before) before :=
    (topTransport.compose pairTransport).workspaceTransport_restrict_readsAs before
  have afterReads : (topTransport.compose pairTransport).ReadsAs
      ((topTransport.compose pairTransport).restrict
        (LatticeBatchRecoveryWorkspaceBody.step input refs before).1)
      (LatticeBatchRecoveryWorkspaceBody.step input refs before).1 :=
    (topTransport.compose pairTransport).workspaceTransport_restrict_readsAs _
  constructor
  · intro shape other avoids
    have deepAvoids : refs.result.key ∉
        ((topTransport.compose pairTransport).liftInput other).storageKeys := by
      simpa only [refs, bodyRefs, Transport.liftWrite_key, Transport.liftInput_storageKeys]
        using avoids
    exact (afterReads other).symm.trans
      ((LatticeBatchRecoveryWorkspaceBody.into_callerFrame input refs before _
        (LatticeBatchRecoveryWorkspaceBody.callerFrame_of_rootInput refs separation other
          deepAvoids)).trans (reads other))
  · intro sample initial
    have parameterStored := (reads parameter).trans initial.parameterValue
    have initialized := bodyInitial input sample refs before parameterStored topInitialized
    have output := (LatticeBatchRecoveryWorkspaceBody.into_correct input sample refs separation
      before initialized).output
    exact (afterReads (FirstAccepted.cellRead result)).symm.trans
      (output.trans (bodyValue_restrict sample refs before))

/-- The canonical actual allocator record follows the complete caller store and emitted path. -/
def step (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) :
    Store ctx → Store ctx × (into ctx input parameter terminals result).Path :=
  Classical.choose (actualRecord_exists input parameter terminals result)

/-- The complete allocated execution equals its actual record on every history and reference. -/
theorem into_execute (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into ctx input parameter terminals result).execute Reference state =
      state.mapClassical (fun entry =>
        ((step input parameter terminals result entry.1).1,
          (entry.2, (step input parameter terminals result entry.1).2))) :=
  (Classical.choose_spec (actualRecord_exists input parameter terminals result)).1 Reference state

/-- Every caller value outside the result survives, without parameter or scratch premises. -/
theorem into_callerFrame (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) (before : Store ctx) :
    CallerFrame result before (step input parameter terminals result before).1 :=
  ((Classical.choose_spec (actualRecord_exists input parameter terminals result)).2 before).1

/-- Actual allocation, complete recovery and release return the original batch value. -/
theorem into_correct (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) (before : Store ctx)
    (initial : InitialConditions input sample before parameter) :
    Relation sample terminals result before (step input parameter terminals result before).1 :=
  ⟨((Classical.choose_spec (actualRecord_exists input parameter terminals result)).2 before).2
    sample initial, into_callerFrame input parameter terminals result before⟩

/-- Independent complete native budget including shared initialization and all 120 pairs. -/
def eventEnvelope (N : Nat) : ResourcePool kind :=
  LatticeBatchRecoveryWorkspaceBody.eventEnvelope N

/-- Independent complete unit-duration dependency bound. -/
def depthBound (N : Nat) : Nat := LatticeBatchRecoveryWorkspaceBody.depthBound N

/-- Independent additional live capacity includes all eight packages and native-power scratch. -/
def additionalSpace (N : Nat) : SpacePool kind :=
  LatticeBatchRecoveryWorkspace.allocationSpace N +
    Modular.NativePower.powerSpace kind (modulusBits N)

/-- Every full actual path satisfies the independent native-coordinate budget. -/
theorem into_pool_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    (into ctx input parameter terminals result).resourcePool path ≤ eventEnvelope N := by
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_pool_le
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
    selected
  exact LatticeBatchRecoveryWorkspaceBody.into_pool_le input _ selected

/-- Actual dependency depth follows shared initialization, every pair, and final output packing. -/
theorem into_depth_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    (into ctx input parameter terminals result).depth (fun _ => 1) path ≤ depthBound N := by
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_depth_le
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
    selected
  exact LatticeBatchRecoveryWorkspaceBody.into_depth_le input _ selected

/-- Resident accounting retains all caller entries and all simultaneously allocated native cells. -/
theorem into_resident_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    (into ctx input parameter terminals result).peakResidentSpace path ≤
      additionalSpace N + ctx.residentSpace := by
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_resident_le
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
    selected
  simpa only [add_comm] using LatticeBatchRecoveryWorkspaceBody.into_resident_le input
    (bodyRefs parameter terminals result top topTransport cells pairTransport) selected

/-- Auxiliary accounting includes every original role and all eight allocated scratch packages. -/
theorem into_auxiliary_le (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (path : (into ctx input parameter terminals result).Path) :
    (into ctx input parameter terminals result).peakAuxiliarySpace path ≤
      additionalSpace N + ctx.auxiliarySpace := by
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_auxiliary_le
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
    selected
  simpa only [add_comm] using LatticeBatchRecoveryWorkspaceBody.into_auxiliary_le input
    (bodyRefs parameter terminals result top topTransport cells pairTransport) selected

/-- Complete lexical release restores every borrowed system jointly with arbitrary references. -/
theorem into_borrowedRestored (input : Input N) (parameter : CInputRef ctx (ParameterShape N))
    (terminals : LatticePairRecoveryBatch.Terminals ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (into ctx input parameter terminals result).BorrowedRestored Reference state
      ((into ctx input parameter terminals result).execute Reference state) := by
  apply LatticeBatchRecoveryWorkspace.withWorkspaces_borrowedRestored
  intro topCtx inner top topDistinct topTransport topSeparated cells pairTransport certificates
    Past inst initial
  exact LatticeBatchRecoveryWorkspaceBody.into_borrowedRestored input _ Reference initial

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedBatchRecoveryMachine
