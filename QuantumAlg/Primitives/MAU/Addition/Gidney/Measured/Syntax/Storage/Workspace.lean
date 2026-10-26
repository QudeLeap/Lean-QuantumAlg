/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Storage
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index

/-!
# Distinct carry-record banks from actual lexical workspace cells

The existing lexical allocator provides the writable cells and their physical
key separation. This adapter changes only the typed indexing interface. The
same cells can be released by the enclosing workspace instructions after both
paid phase passes [G25, main.tex:271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.RecordBank

noncomputable section

open Execution ClassicalWorkspace

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {records : Nat}

private lemma castCell_key {source target : CShape} (same : source = target)
    (cell : Cell ctx source) :
    ((same ▸ cell : Cell ctx target).ref).key = cell.ref.key := by
  cases same
  rfl

private lemma cellAtOfFn_key (shape : Fin records → CShape)
    (cells : Cells ctx (List.ofFn shape)) (index : Fin records) :
    (cellAtOfFn shape cells index).ref.key =
      (cellAt cells (Fin.cast (by simp) index)).ref.key := by
  unfold cellAtOfFn
  exact castCell_key _ _

/-- The lexical allocator's actual finite cells supply a distinct bank without retained output. -/
def ofWorkspace (cells : Cells ctx (List.ofFn fun _ : Fin records => CShape.finite 2))
    (distinct : cells.Distinct) : RecordBank ctx records where
  output := refAt (fun _ : Fin records => CShape.finite 2) cells
  distinct := by
    intro first second same
    have actual :
        (cellAt cells (Fin.cast (by simp) first)).ref.key =
          (cellAt cells (Fin.cast (by simp) second)).ref.key :=
      (cellAtOfFn_key _ cells first).symm.trans (same.trans (cellAtOfFn_key _ cells second))
    have indices := workspaceCells_cellAt_key_injective cells distinct actual
    have values := congrArg
      (fun value : Fin (List.ofFn fun _ : Fin records => CShape.finite 2).length => value.val)
      indices
    exact Fin.ext values

end

end QuantumAlg.MAU.Addition.Gidney.Measured.RecordBank
