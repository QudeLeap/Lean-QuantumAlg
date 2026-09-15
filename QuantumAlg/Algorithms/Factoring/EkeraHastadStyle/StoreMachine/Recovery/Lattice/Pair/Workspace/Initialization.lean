/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core.Initialization

/-!
# Actual canonical initial values of all six pair-recovery packages
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace

open Execution
open Execution.ClassicalWorkspace

/-- Lift all six actual cell packages through the same structural scope map. -/
def Cells.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind} {N : Nat}
    (cells : Cells outer N) (transport : Transport outer inner) : Cells inner N where
  core := cells.core.transport transport
  target := transportCells transport cells.target
  lll := transportCells transport cells.lll
  nearest := transportCells transport cells.nearest

/-- Every actual package contains its shapes' canonical initial values. -/
structure Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (store : Store ctx) (cells : Cells ctx N) : Prop where
  core : LatticePairCoreWorkspace.Initialized store cells.core
  target : cells.target.Initialized store
  lll : cells.lll.Initialized store
  nearest : cells.nearest.Initialized store

/-- Actual read agreement carries every package's initial values through a further scope. -/
theorem Initialized.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind} {N : Nat}
    {source : Store outer} {before : Store inner} {cells : Cells outer N}
    (initial : Initialized source cells) (transport : Transport outer inner)
    (reads : transport.ReadsAs source before) :
    Initialized before (cells.transport transport) where
  core := initial.core.transport transport reads
  target := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.target reads initial.target
  lll := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.lll reads initial.lll
  nearest := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.nearest reads initial.nearest

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairRecoveryWorkspace
