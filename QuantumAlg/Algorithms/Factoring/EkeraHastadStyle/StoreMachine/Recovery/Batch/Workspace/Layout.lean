/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Selection.Seed
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Fold.Workspace

/-!
# Physical six-cell persistent batch layout

The actual allocator supplies the original six cells in stable order. The
canonical first-accepted selector occupies four of them, with a separate
widening word and final narrowing word. Distinct allocation keys establish
all local selection and output separation without caller value assumptions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceLayout

open Execution
open Execution.ClassicalWorkspace
open ClassicalRoutines

noncomputable section

/-- Width of the persistent factor selector used by all 120 pair slots. -/
abbrev FactorWidth (N : Nat) : Nat :=
  LatticePairRecoveryFold.FactorWidth N

/-- Top-level workspace cells in stable data-flow order. -/
def topShapes (N : Nat) : List CShape :=
  [.unsignedWord (FactorWidth N), .bit, .unsignedWord (FactorWidth N),
    .bit, .bit, .unsignedWord (modulusBits N)]

/-- Heterogeneous storage allocated for the top-level recovery state. -/
abbrev TopCells {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :=
  Execution.ClassicalWorkspace.Cells ctx (topShapes N)

/-- Index of the wide cell in the local workspace. -/
def wideIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨0, by simp [topShapes]⟩

/-- Index of the accepted cell in the local workspace. -/
def acceptedIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨1, by simp [topShapes]⟩

/-- Index of the selected cell in the local workspace. -/
def selectedIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨2, by simp [topShapes]⟩

/-- Index of the available cell in the local workspace. -/
def availableIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨3, by simp [topShapes]⟩

/-- Index of the take cell in the local workspace. -/
def takeIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨4, by simp [topShapes]⟩

/-- Index of the narrow cell in the local workspace. -/
def narrowIndex (N : Nat) : Fin (topShapes N).length :=
  ⟨5, by simp [topShapes]⟩

/-- Workspace word receiving the sampler's modulus-width early factor. -/
def wideCandidate {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx (.unsignedWord (FactorWidth N)) :=
  (cellAt cells (wideIndex N)).ref

/-- Persistent factor-accepted latch shared by seed and all pair slots. -/
def accepted {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx .bit :=
  (cellAt cells (acceptedIndex N)).ref

/-- Persistent wide factor word shared by seed and all pair slots. -/
def selected {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx (.unsignedWord (FactorWidth N)) :=
  (cellAt cells (selectedIndex N)).ref

/-- Selector scratch latch recording that no factor has yet been selected. -/
def available {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx .bit :=
  (cellAt cells (availableIndex N)).ref

/-- Selector scratch latch controlling the persistent update. -/
def take {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx .bit :=
  (cellAt cells (takeIndex N)).ref

/-- Modulus-width word used by the final option packer. -/
def narrow {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : CWriteRef ctx (.unsignedWord (modulusBits N)) :=
  (cellAt cells (narrowIndex N)).ref

/-- The real persistent first-success selector over the top workspace cells. -/
def factorSelection {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : FirstAccepted.Refs ctx (FactorWidth N) where
  accepted := accepted cells
  selected := selected cells
  available := available cells
  take := take cells

/-- Early-factor seed wired to the shared persistent selector. -/
def seedRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) : LatticeEarlyFactorSeed.Refs ctx N where
  wideCandidate := wideCandidate cells
  selection := factorSelection cells

/-- Final output packer wired to the same selector and a caller result cell. -/
def outputRefs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) :
    LatticeBatchRecoveryOutput.Refs ctx N where
  selection := factorSelection cells
  narrow := narrow cells
  result := result

private theorem keyNe {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) (distinct : cells.Distinct)
    {left right : Fin (topShapes N).length} (different : left ≠ right) :
    (cellAt cells left).ref.key ≠ (cellAt cells right).ref.key :=
  fun equal => different (workspaceCells_cellAt_key_injective cells distinct equal)

private theorem readAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (source : CWriteRef ctx shape) {key : StorageKey}
    (different : source.key ≠ key) : key ∉ (FirstAccepted.cellRead source).storageKeys := by
  simpa only [FirstAccepted.cellRead, CInputRef.storageKeys, List.mem_singleton, ne_comm]
    using different

/-- Actual distinct allocation supplies exactly the canonical selector inequalities. -/
theorem selectorSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) (distinct : cells.Distinct) :
    LatticePairFactorWorkspaceSeparation.SelectorSeparation (factorSelection cells) := by
  constructor
  · exact keyNe cells distinct (left := availableIndex N) (right := acceptedIndex N)
      (by simp [availableIndex, acceptedIndex])
  · exact keyNe cells distinct (left := takeIndex N) (right := acceptedIndex N)
      (by simp [takeIndex, acceptedIndex])
  · exact keyNe cells distinct (left := availableIndex N) (right := selectedIndex N)
      (by simp [availableIndex, selectedIndex])
  · exact keyNe cells distinct (left := takeIndex N) (right := selectedIndex N)
      (by simp [takeIndex, selectedIndex])
  · exact keyNe cells distinct (left := acceptedIndex N) (right := selectedIndex N)
      (by simp [acceptedIndex, selectedIndex])

/-- The retained parameter and actual top-cell distinctness supply the complete seed contract. -/
theorem seedSeparation {kind : ProblemKind} {outer ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (parameter : CInputRef outer (ParameterShape N)) :
    LatticeEarlyFactorSeed.Separation (transport.liftInput parameter) (seedRefs cells) := by
  have parameterAvoids (index : Fin (topShapes N).length) :
      (cellAt cells index).ref.key ∉ (transport.liftInput parameter).storageKeys :=
    Cells.workspaceCells_cellAt_transport_avoids cells transport separated parameter index
  have wideAvoids (index : Fin (topShapes N).length) (different : wideIndex N ≠ index) :
      (cellAt cells index).ref.key ∉ (FirstAccepted.cellRead (wideCandidate cells)).storageKeys :=
    readAvoids _ (keyNe cells distinct different)
  have selector := selectorSeparation cells distinct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact parameterAvoids (wideIndex N)
  · exact parameterAvoids (wideIndex N)
  · apply readAvoids
    exact keyNe cells distinct (left := acceptedIndex N) (right := wideIndex N)
      (by simp [acceptedIndex, wideIndex])
  · apply readAvoids
    exact keyNe cells distinct (left := selectedIndex N) (right := wideIndex N)
      (by simp [selectedIndex, wideIndex])
  · exact {
      availableEligible := parameterAvoids (availableIndex N)
      availableCandidate := wideAvoids (availableIndex N) (by simp [wideIndex, availableIndex])
      takeCandidate := wideAvoids (takeIndex N) (by simp [wideIndex, takeIndex])
      availableAccepted := selector.availableAccepted
      takeAccepted := selector.takeAccepted
      availableSelected := selector.availableSelected
      takeSelected := selector.takeSelected
      acceptedSelected := selector.acceptedSelected }

/-- Top-cell distinctness supplies the final packer's only local separation requirement. -/
theorem outputSeparation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (cells : TopCells ctx N) (distinct : cells.Distinct)
    (result : CWriteRef ctx (LatticeBatchRecoveryOutput.OutputShape N)) :
    LatticeBatchRecoveryOutput.Separation (outputRefs cells result) := by
  constructor
  apply readAvoids
  exact keyNe cells distinct (left := acceptedIndex N) (right := narrowIndex N)
    (by simp [acceptedIndex, narrowIndex])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeBatchRecoveryWorkspaceLayout
