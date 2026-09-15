/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Initialization.State
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Package
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# Reading the same XGCD state across actual lexical transports

The relation compares all transported reads of real stores. Both the
mathematical state and its separate activity bit are unchanged when the
seven live cells are viewed through that structural transport.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {outer inner : RuntimeCtx kind} {width : Nat}

private theorem transported_read (transport : Transport outer inner)
    (cells : Cells outer (stateShapes width)) (before : Store outer) (after : Store inner)
    (reads : transport.ReadsAs before after) (index : Fin (stateShapes width).length) :
    after.read (GCD.cellRead (cellAt (transportCells transport cells) index).ref) =
      before.read (GCD.cellRead (cellAt cells index).ref) := by
  rw [workspaceCells_cellAt_transportCells_ref]
  exact reads (GCD.cellRead (cellAt cells index).ref)

/-- Structural transport preserves the decoded six-field state of the actual live cells. -/
theorem xgcdNativeState_transport (transport : Transport outer inner)
    (cells : Cells outer (stateShapes width)) (before : Store outer) (after : Store inner)
    (reads : transport.ReadsAs before after) :
    storedState (transportCells transport cells) after = storedState cells before := by
  have first : after.read (GCD.cellRead (firstCell (transportCells transport cells))) =
      before.read (GCD.cellRead (firstCell cells)) :=
    transported_read transport cells before after reads ⟨0, by change 0 < 7; decide⟩
  have second : after.read (GCD.cellRead (secondCell (transportCells transport cells))) =
      before.read (GCD.cellRead (secondCell cells)) :=
    transported_read transport cells before after reads ⟨1, by change 1 < 7; decide⟩
  have firstLeft : after.read (GCD.cellRead (firstLeftCell (transportCells transport cells))) =
      before.read (GCD.cellRead (firstLeftCell cells)) :=
    transported_read transport cells before after reads ⟨2, by change 2 < 7; decide⟩
  have firstRight : after.read (GCD.cellRead (firstRightCell (transportCells transport cells))) =
      before.read (GCD.cellRead (firstRightCell cells)) :=
    transported_read transport cells before after reads ⟨3, by change 3 < 7; decide⟩
  have secondLeft : after.read (GCD.cellRead (secondLeftCell (transportCells transport cells))) =
      before.read (GCD.cellRead (secondLeftCell cells)) :=
    transported_read transport cells before after reads ⟨4, by change 4 < 7; decide⟩
  have secondRight : after.read (GCD.cellRead (secondRightCell (transportCells transport cells))) =
      before.read (GCD.cellRead (secondRightCell cells)) :=
    transported_read transport cells before after reads ⟨5, by change 5 < 7; decide⟩
  unfold storedState
  rw [first, second, firstLeft, firstRight, secondLeft, secondRight]

/-- The actual activity read is preserved through the same structural scope transport. -/
theorem xgcdNativeState_activity_transport (transport : Transport outer inner)
    (cells : Cells outer (stateShapes width)) (before : Store outer) (after : Store inner)
    (reads : transport.ReadsAs before after) :
    after.read (GCD.cellRead (activeCell (transportCells transport cells))) =
      before.read (GCD.cellRead (activeCell cells)) :=
  transported_read transport cells before after reads ⟨6, by change 6 < 7; decide⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
