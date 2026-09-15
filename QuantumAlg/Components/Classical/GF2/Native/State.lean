/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Actual seven-cell GF(2) recovery workspace

The original allocation order is pivot rows, matrix, used rows, pivot mask,
candidate, zero word, then success bit. The existing allocator takes its list
in deepest-first order, so this list is the reverse of that chronology.
All seven cells are genuinely initialized and released around the existing
actual into circuit; no caller workspace or initial-zero promise is added.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

/-- The original seven real workspaces, listed in deepest-first stack order. -/
def stateShapes (rowCount width : Nat) : List CShape :=
  [.bit, .unsignedWord width, .unsignedWord width, .unsignedWord width,
    .unsignedWord rowCount, .fixedVector rowCount (.unsignedWord width),
    .fixedVector width (.unsignedWord rowCount)]

/-- The original actual body uses the allocated cells and only structural caller lifts. -/
def stateBody (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (output : CWriteRef ctx (.option (.unsignedWord width)))
    {inner : RuntimeCtx kind} (cells : ClassicalWorkspace.Cells inner (stateShapes rowCount width))
    (transport : Transport ctx inner) : Circuit inner inner :=
  into (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output)

/-- All seven original scopes enclose the actual complete same-context recovery. -/
def withState (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (output : CWriteRef ctx (.option (.unsignedWord width))) : Circuit ctx ctx :=
  ClassicalWorkspace.withCells ctx (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)

end QuantumAlg.ClassicalRoutines.GF2.Native
