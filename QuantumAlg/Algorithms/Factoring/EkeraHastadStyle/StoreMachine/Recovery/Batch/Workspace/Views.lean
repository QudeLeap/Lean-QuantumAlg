/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Tail
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Shared.Workspace

/-!
# Deep views of the fixed-batch recovery workspace

The six persistent top cells are allocated before the reusable pair package.
This module transports the live top package into the deepest scope and exposes
the shared initializer, seeded tail, and indexed pair-fold references there.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeBatchRecoveryWorkspaceViews

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

/-- Compose the persistent-top and reusable-pair transports. -/
def deepTransport {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner) :
    Transport root inner :=
  topTransport.compose pairTransport

/-- The persistent top cells viewed in the reusable-pair scope. -/
def topAt {kind : ProblemKind} {topCtx inner : RuntimeCtx kind} {N : Nat}
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N) :
    LatticeBatchRecoveryWorkspaceLayout.TopCells inner N :=
  transportCells pairTransport top

/-- The retained parameter viewed in the reusable-pair scope. -/
def parameterAt {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (parameter : CInputRef root (ParameterShape N)) :
    CInputRef inner (ParameterShape N) :=
  pairTransport.liftInput (topTransport.liftInput parameter)

/-- All retained terminal cells viewed in the reusable-pair scope. -/
def terminalsAt {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (terminals : LatticePairRecoveryBatch.Terminals root N) :
    LatticePairRecoveryBatch.Terminals inner N :=
  LatticePairRecoveryFoldWorkspace.liftTerminals pairTransport
    (LatticeBatchRecoveryWorkspace.terminalsAt topTransport terminals)

/-- Shared modular and quadratic initialization in the deepest scope. -/
def initializationRefs {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeSharedQuadraticInitialization.Refs inner N :=
  LatticeSharedQuadraticWorkspace.refs cells.pair.core.shared cells.quadratic
    (deepTransport topTransport pairTransport) parameter

/-- The 120 indexed pair views over one reusable physical allocation. -/
def foldRefs {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticePairRecoveryFold.Refs inner N :=
  LatticePairRecoveryFoldWorkspace.refs pairTransport cells
    (LatticeBatchRecoveryWorkspaceLayout.factorSelection top)
    (LatticeBatchRecoveryWorkspace.terminalsAt topTransport terminals)
    (LatticeBatchRecoveryWorkspace.parameterAt topTransport parameter)

/-- Top-cell distinctness survives allocation of the reusable pair package. -/
theorem topAt_distinct {kind : ProblemKind}
    {topCtx inner : RuntimeCtx kind} {N : Nat}
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topDistinct : top.Distinct) :
    (topAt pairTransport top).Distinct :=
  workspaceCells_transportCells_distinct pairTransport top topDistinct

/-- Caller separation of the top package survives the deeper allocation. -/
theorem topAt_separated {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topSeparated : top.TransportSeparated topTransport) :
    (topAt pairTransport top).TransportSeparated
      (deepTransport topTransport pairTransport) :=
  workspaceCells_transportCells_transportSeparated topTransport
    pairTransport top topSeparated

/-- Physical pair certificates supply the shared initializer contract. -/
theorem initializationSeparation {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeSharedQuadraticInitialization.Separation
      (initializationRefs topTransport pairTransport cells parameter) := by
  exact LatticeSharedQuadraticWorkspace.separation cells.pair.core.shared
    certificates.pair.core.sharedDistinct cells.quadratic certificates.quadraticDistinct
    (deepTransport topTransport pairTransport)
    (workspaceCells_transportSeparated_compose topTransport pairTransport
      cells.pair.core.shared certificates.pair.core.sharedSeparated)
    (workspaceCells_transportSeparated_compose topTransport pairTransport
      cells.quadratic certificates.quadraticSeparated)
    certificates.coreQuadratic.shared parameter

/-- The physical top and pair packages supply all 120 fold certificates. -/
theorem foldSeparation {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topDistinct : top.Distinct)
    (topSeparated : top.TransportSeparated topTransport)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticePairRecoveryFold.Separation
      (foldRefs topTransport pairTransport top cells terminals parameter) := by
  exact LatticePairRecoveryFoldWorkspace.separation certificates
    (LatticeBatchRecoveryWorkspaceLayout.factorSelection top)
    (LatticeBatchRecoveryWorkspaceLayout.selectorSeparation top topDistinct)
    (LatticeBatchRecoveryWorkspace.terminalsAt topTransport terminals)
    (LatticeBatchRecoveryWorkspace.parameterAt topTransport parameter)
    (LatticeBatchRecoveryWorkspace.factorFrames top topTransport topSeparated
      terminals parameter)

/-- The transported top package supplies the early-factor seed contract. -/
theorem seedSeparation {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topDistinct : top.Distinct)
    (topSeparated : top.TransportSeparated topTransport)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeEarlyFactorSeed.Separation
      (parameterAt topTransport pairTransport parameter)
      (LatticeBatchRecoveryWorkspaceLayout.seedRefs
        (topAt pairTransport top)) := by
  simpa only [parameterAt, deepTransport, Transport.liftInput_compose] using
    (LatticeBatchRecoveryWorkspaceLayout.seedSeparation
      (topAt pairTransport top) (topAt_distinct pairTransport top topDistinct)
      (deepTransport topTransport pairTransport)
      (topAt_separated topTransport pairTransport top topSeparated) parameter)

/-- Every root-scope input frames the transported early-factor seed. -/
private theorem seedCallerFrame_of_rootInput {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat} {shape : CShape}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topSeparated : top.TransportSeparated topTransport)
    (input : CInputRef root shape) :
    LatticeEarlyFactorSeed.CallerFrameAvoids
      (LatticeBatchRecoveryWorkspaceLayout.seedRefs
        (topAt pairTransport top))
      ((deepTransport topTransport pairTransport).liftInput input) := by
  have avoids (index : Fin
      (LatticeBatchRecoveryWorkspaceLayout.topShapes N).length) :
      (cellAt (topAt pairTransport top) index).ref.key ∉
        ((deepTransport topTransport pairTransport).liftInput input).storageKeys :=
    ClassicalWorkspace.Cells.workspaceCells_cellAt_transport_avoids (topAt pairTransport top)
      (deepTransport topTransport pairTransport)
      (topAt_separated topTransport pairTransport top topSeparated) input index
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.wideCandidate] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.wideIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.accepted] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.selected] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.selectedIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.available] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.availableIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.take] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.takeIndex N)

/-- A fresh inner workspace cell avoids every transported top cell. -/
private theorem innerCell_avoids_top {kind : ProblemKind}
    {topCtx inner : RuntimeCtx kind} {N : Nat} {shapes : List CShape}
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (cells : ClassicalWorkspace.Cells inner shapes)
    (cellsSeparated : cells.TransportSeparated pairTransport)
    (cellIndex : Fin shapes.length)
    (topIndex : Fin
      (LatticeBatchRecoveryWorkspaceLayout.topShapes N).length) :
    (cellAt (topAt pairTransport top) topIndex).ref.key ∉
      (FirstAccepted.cellRead (cellAt cells cellIndex).ref).storageKeys := by
  simpa only [topAt, FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton] using
    (crossSeparated_of_nested pairTransport top cells cellsSeparated).keysNe topIndex cellIndex

/-- Every fresh inner workspace cell frames the early-factor seed. -/
private theorem seedCallerFrame_of_innerCell {kind : ProblemKind}
    {topCtx inner : RuntimeCtx kind} {N : Nat} {shapes : List CShape}
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (cells : ClassicalWorkspace.Cells inner shapes)
    (cellsSeparated : cells.TransportSeparated pairTransport)
    (cellIndex : Fin shapes.length) :
    LatticeEarlyFactorSeed.CallerFrameAvoids
      (LatticeBatchRecoveryWorkspaceLayout.seedRefs
        (topAt pairTransport top))
      (FirstAccepted.cellRead (cellAt cells cellIndex).ref) := by
  have avoids := innerCell_avoids_top pairTransport top cells cellsSeparated
    cellIndex
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.wideCandidate] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.wideIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.accepted] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.acceptedIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.selected] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.selectedIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.available] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.availableIndex N)
  · simpa only [LatticeBatchRecoveryWorkspaceLayout.seedRefs,
      LatticeBatchRecoveryWorkspaceLayout.factorSelection,
      LatticeBatchRecoveryWorkspaceLayout.take] using
      avoids (LatticeBatchRecoveryWorkspaceLayout.takeIndex N)

/-- Transporting the top package transports its persistent selector. -/
theorem factorSelection_topAt {kind : ProblemKind}
    {topCtx inner : RuntimeCtx kind} {N : Nat}
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N) :
    LatticeBatchRecoveryWorkspaceLayout.factorSelection
        (topAt pairTransport top) =
      LatticePairFactorWorkspaceSeparation.liftSelection pairTransport
        (LatticeBatchRecoveryWorkspaceLayout.factorSelection top) := by
  cases top with
  | cons wide tail =>
    cases tail with
    | cons accepted tail =>
      cases tail with
      | cons selected tail =>
        cases tail with
        | cons available tail =>
          cases tail with
          | cons take tail =>
            cases tail with
            | cons narrow tail =>
              cases tail
              rfl

/-- Seeded batch-tail references in the deepest physical scope. -/
def tailRefs {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeBatchRecoveryTail.Refs inner N where
  parameter := parameterAt topTransport pairTransport parameter
  terminals := terminalsAt topTransport pairTransport terminals
  seed := LatticeBatchRecoveryWorkspaceLayout.seedRefs
    (topAt pairTransport top)
  fold := foldRefs topTransport pairTransport top cells terminals parameter
  sharedSelection := factorSelection_topAt pairTransport top
  aligned := LatticePairRecoveryFoldWorkspace.aligned pairTransport cells
    (LatticeBatchRecoveryWorkspaceLayout.factorSelection top)
    (LatticeBatchRecoveryWorkspace.terminalsAt topTransport terminals)
    (LatticeBatchRecoveryWorkspace.parameterAt topTransport parameter)

/-- The seed preserves every persistent entry fact used by every pair. -/
private theorem seedInitialFrames {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topSeparated : top.TransportSeparated topTransport)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    ∀ index, LatticeBatchRecoveryTail.SeedInitialFrameAvoids
      (tailRefs topTransport pairTransport top cells terminals parameter).seed
      (((tailRefs topTransport pairTransport top cells terminals
        parameter).fold).pair index) := by
  let seed := LatticeBatchRecoveryWorkspaceLayout.seedRefs
    (topAt pairTransport top)
  have parameterFrame : LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (parameterAt topTransport pairTransport parameter) := by
    simpa only [parameterAt, deepTransport, Transport.liftInput_compose] using
      (seedCallerFrame_of_rootInput topTransport pairTransport top topSeparated parameter)
  have baseFrame : LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (CInputRef.first (parameterAt topTransport pairTransport parameter)) :=
    { wideCandidate := parameterFrame.wideCandidate
      accepted := parameterFrame.accepted
      selected := parameterFrame.selected
      available := parameterFrame.available
      take := parameterFrame.take }
  have quadraticFrame (cell : QuadraticScratchLayout.Cell) :
      LatticeEarlyFactorSeed.CallerFrameAvoids seed
        (FirstAccepted.cellRead
          (QuadraticScratchLayout.cellRef cells.quadratic cell)) := by
    exact seedCallerFrame_of_innerCell pairTransport top cells.quadratic
      certificates.quadraticSeparated
      (QuadraticScratchLayout.cellIndex N cell)
  intro index
  refine {
    setupParameter := ?_
    setupBase := ?_
    quadraticModulus := ?_
    firstOne := ?_
    firstModulus := ?_
    firstZero := ?_
    secondOne := ?_
    secondModulus := ?_
    secondZero := ?_ }
  · exact parameterFrame
  · exact baseFrame
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.modulusInput cells.quadratic)
    exact quadraticFrame .modulus
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.oneInput cells.quadratic)
    exact quadraticFrame .one
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.modulusInput cells.quadratic)
    exact quadraticFrame .modulus
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.zeroInput cells.quadratic)
    exact quadraticFrame .zero
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.oneInput cells.quadratic)
    exact quadraticFrame .one
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.modulusInput cells.quadratic)
    exact quadraticFrame .modulus
  · change LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (QuadraticScratchViews.zeroInput cells.quadratic)
    exact quadraticFrame .zero

/-- The seed preserves every structural bit of every terminal cell. -/
private theorem seedTerminalFrames {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topSeparated : top.TransportSeparated topTransport)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeBatchRecoveryTail.SeedTerminalFrameAvoids
      (tailRefs topTransport pairTransport top cells terminals parameter) := by
  constructor
  intro terminalIndex bitIndex
  let seed := LatticeBatchRecoveryWorkspaceLayout.seedRefs
    (topAt pairTransport top)
  have terminalFrame : LatticeEarlyFactorSeed.CallerFrameAvoids seed
      (pairTransport.liftInput (topTransport.liftInput (terminals terminalIndex))) := by
    simpa only [deepTransport, Transport.liftInput_compose] using
      (seedCallerFrame_of_rootInput topTransport pairTransport top topSeparated
        (terminals terminalIndex))
  change LatticeEarlyFactorSeed.CallerFrameAvoids seed
    (.bitsGet (pairTransport.liftInput (topTransport.liftInput
      (terminals terminalIndex))) bitIndex)
  exact {
    wideCandidate := terminalFrame.wideCandidate
    accepted := terminalFrame.accepted
    selected := terminalFrame.selected
    available := terminalFrame.available
    take := terminalFrame.take }

/-- The complete physical allocation supplies the seeded-tail separation. -/
theorem tailSeparation {kind : ProblemKind}
    {root topCtx inner : RuntimeCtx kind} {N : Nat}
    (topTransport : Transport root topCtx)
    (pairTransport : Transport topCtx inner)
    (top : LatticeBatchRecoveryWorkspaceLayout.TopCells topCtx N)
    (topDistinct : top.Distinct)
    (topSeparated : top.TransportSeparated topTransport)
    (cells : LatticePairFactorWorkspaceSeparation.Cells inner N)
    (certificates :
      LatticePairFactorWorkspaceSeparation.Certificates pairTransport cells)
    (terminals : LatticePairRecoveryBatch.Terminals root N)
    (parameter : CInputRef root (ParameterShape N)) :
    LatticeBatchRecoveryTail.Separation
      (tailRefs topTransport pairTransport top cells terminals parameter) where
  seed := seedSeparation topTransport pairTransport top topDistinct topSeparated
    parameter
  fold := foldSeparation topTransport pairTransport top topDistinct topSeparated
    cells certificates terminals parameter
  seedInitialFrames := seedInitialFrames topTransport pairTransport top
    topSeparated cells certificates terminals parameter
  seedTerminalFrames := seedTerminalFrames topTransport pairTransport top
    topSeparated cells terminals parameter

end

end LatticeBatchRecoveryWorkspaceViews
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
