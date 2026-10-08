/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace.Body.Frames
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Pairs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Shared.Workspace.Layout

/-!
# Correctness of the actual allocated recovery body

Shared initialization supplies the original modular setup and quadratic
constants while preserving all retained terminal bits and the persistent
factor latch. The complete seeded endpoint therefore emits the exact original
fixed-batch value in the same final store as every preserved caller read.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody

open Execution
open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {root topCtx inner : RuntimeCtx model.kind} {N : Nat}

omit [BitWord.Selected model] in
private theorem initialization_parameter_eq (refs : Refs root topCtx inner N) :
    (initializationRefs refs).setup.parameter =
      LatticeBatchRecoveryWorkspaceViews.parameterAt refs.topTransport refs.pairTransport
        refs.parameter :=
  ClassicalWorkspace.Transport.liftInput_compose refs.topTransport refs.pairTransport refs.parameter

omit [BitWord.Selected model] in
private theorem pairSetup_eq (refs : Refs root topCtx inner N)
    (index : Fin LatticePairRecoveryFold.PairCount) :
    ((endpointRefs refs).tail.fold.pair index).pair.setup = (initializationRefs refs).setup := by
  change LatticeCandidateSharedWorkspaceLayout.setupRefs refs.cells.pair.core.shared
      refs.pairTransport (refs.topTransport.liftInput refs.parameter) =
    LatticeCandidateSharedWorkspaceLayout.setupRefs refs.cells.pair.core.shared
      (refs.topTransport.compose refs.pairTransport) refs.parameter
  unfold LatticeCandidateSharedWorkspaceLayout.setupRefs
  rw [ClassicalWorkspace.Transport.liftInput_compose]

private theorem preparedSamples_afterInitialization (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs root topCtx inner N)
    (separation : Separation refs) (store : Store inner) :
    LatticePairRecoveryBatch.preparedSamples (preparedResidue sample)
        (endpointRefs refs).tail.terminals
        (LatticeSharedQuadraticInitialization.step (model := model)
          input (initializationRefs refs) store).1 =
      LatticePairRecoveryBatch.preparedSamples (preparedResidue sample)
        (endpointRefs refs).tail.terminals store := by
  apply List.Vector.ext
  intro terminalIndex
  simp only [LatticePairRecoveryBatch.preparedSamples, List.Vector.get_map, List.Vector.get_ofFn]
  apply congrArg
  funext bitIndex
  unfold BatchMachine.sourceBits
  have terminalFrame := initializationCallerFrame_of_topInput refs separation
    (refs.topTransport.liftInput (refs.terminals terminalIndex))
  have bitFrame : LatticeSharedQuadraticInitialization.CallerFrameAvoids
      (initializationRefs refs)
      (.bitsGet ((endpointRefs refs).tail.terminals terminalIndex) bitIndex) :=
    ⟨terminalFrame.setup, terminalFrame.quadratic.modulus,
      terminalFrame.quadratic.one, terminalFrame.quadratic.zero⟩
  exact congrArg CShape.Value.toBool
    (LatticeSharedQuadraticInitialization.into_callerFrame (model := model)
      input (initializationRefs refs)
      store _ bitFrame)

/-- Shared initialization and the complete endpoint realize the original shaped batch value. -/
theorem into_correct (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs root topCtx inner N) (separation : Separation refs) (store : Store inner)
    (initial : InitialConditions input sample refs store) :
    Relation sample refs store (step (model := model) input refs store).1 := by
  let middle := (LatticeSharedQuadraticInitialization.step (model := model)
    input (initializationRefs refs) store).1
  have initializationSeparation := LatticeBatchRecoveryWorkspaceViews.initializationSeparation
    refs.topTransport refs.pairTransport refs.cells separation.cells refs.parameter
  have initialized := LatticeSharedQuadraticInitialization.into_correct (model := model) input
    (initializationRefs refs) initializationSeparation store initial.initialization
  have parameterFrame : middle.read (initializationRefs refs).setup.parameter =
      store.read (initializationRefs refs).setup.parameter :=
    initialized.callerFrame _
      ⟨initializationSeparation.setup.parameterAvoidsMutable,
        initializationSeparation.parameterQuadratic⟩
  have storedParameter : store.read (initializationRefs refs).setup.parameter =
      parameterValue input sample := by
    rw [initialization_parameter_eq]
    exact initial.parameterValue
  have acceptedFrame : middle.read
      (FirstAccepted.cellRead (endpointRefs refs).tail.fold.factorSelection.accepted) =
    store.read (FirstAccepted.cellRead (endpointRefs refs).tail.fold.factorSelection.accepted) :=
    initialized.callerFrame _
      (initializationCallerFrame_of_topInput refs separation
        (FirstAccepted.cellRead
          (LatticeBatchRecoveryWorkspaceLayout.factorSelection refs.top).accepted))
  have foldInitial : LatticePairRecoveryFold.InitialConditions input
      (preparedResidue sample).unit middle (endpointRefs refs).tail.fold := by
    intro index
    refine ⟨?_, ?_, ?_⟩
    · rw [pairSetup_eq]
      exact initialized.initial
    · rw [pairSetup_eq, parameterFrame, storedParameter]
      exact (parameterUnit_parameterValue input sample).symm
    · change QuadraticRecoveryGuarded.InitialConditions N middle
        (QuadraticScratchViews.guardedRefs (initializationRefs refs).quadratic _ _)
      exact LatticeSharedQuadraticInitialization.guardedInitialConditions_of_relation
        input (initializationRefs refs) _ _ store middle initialized
  have tailInitial : LatticeBatchRecoveryTail.InitialConditions input sample middle
      (endpointRefs refs).tail := by
    refine ⟨?_, foldInitial, ?_⟩
    · change middle.read (LatticeBatchRecoveryWorkspaceViews.parameterAt
        refs.topTransport refs.pairTransport refs.parameter) = _
      rw [← initialization_parameter_eq]
      exact parameterFrame.trans storedParameter
    · rw [acceptedFrame]
      exact initial.factorInitiallyClear
  have endpointHolds := LatticeBatchRecoveryEndpoint.into_correct (model := model)
    input sample (endpointRefs refs)
    (endpointSeparation refs separation) middle tailInitial
  refine ⟨?_, into_callerFrame (model := model) input refs store⟩
  rw [step_store]
  refine endpointHolds.output.trans ?_
  unfold LatticeBatchRecoveryEndpoint.batchOutputValue
  exact congrArg (fun samples => LatticeBatchRecoveryOutput.outputValue
      (BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N) samples))
    (preparedSamples_afterInitialization input sample refs separation store)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceBody
