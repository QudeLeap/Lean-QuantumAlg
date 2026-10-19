/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Workspace.Core
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Initialization

/-!
# Actual canonical initial values of the three pair-core packages
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace

open Execution
open Execution.ClassicalWorkspace

/-- Initial values read from the actual shared, candidate-slot and pair-state cells. -/
structure Initialized {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (store : Store ctx) (cells : Cells ctx N) : Prop where
  shared : cells.shared.Initialized store
  slot : cells.slot.Initialized store
  state : cells.state.Initialized store

/-- Actual read agreement preserves initialization of all three transported packages. -/
lemma Initialized.transport {kind : ProblemKind} {outer inner : RuntimeCtx kind} {N : Nat}
    {source : Store outer} {before : Store inner} {cells : Cells outer N}
    (initial : Initialized source cells) (transport : Transport outer inner)
    (reads : transport.ReadsAs source before) :
    Initialized before (cells.transport transport) where
  shared := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.shared reads initial.shared
  slot := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.slot reads initial.slot
  state := Execution.ClassicalWorkspace.Cells.workspaceCells_initialized_transport
    transport cells.state reads initial.state

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCoreWorkspace
