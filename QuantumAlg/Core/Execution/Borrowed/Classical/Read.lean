/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Context.Union.Store

/-!
# Reading the actual borrowed classical frame

When the left context contains no borrowed classical cell, the complete
borrowed observation of its disjoint union is precisely the observation of
the real right store. The proof traverses the existing heterogeneous cells.
Heterogeneous equality records only the structural shape equality and does
not insert a runtime cast, allocation, read instruction or replacement store.
-/

namespace QuantumAlg.Execution.ContextUnion

private theorem readBorrowedCells_join_of_empty {kind : ProblemKind}
    (left right : List (RuntimeEntry kind))
    (first : Cells left) (second : Cells right)
    (empty : left.flatMap RuntimeEntry.borrowedClassicalCells = []) :
    HEq (readBorrowedCells (left ++ right) (joinCells left right first second))
      (readBorrowedCells right second) := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      have parts := List.append_eq_nil_iff.mp
        (show head.borrowedClassicalCells ++
          tail.flatMap RuntimeEntry.borrowedClassicalCells = [] from empty)
      cases head with
      | storage key role shape =>
          cases role with
          | borrowedInput => simp [RuntimeEntry.borrowedClassicalCells] at parts
          | workspace | retained | finalOutput => exact ih first.2 parts.2
      | borrowedLayout | suppliedLayout | ownedLayout | ownedCopies => exact ih first.2 parts.2

variable {kind : ProblemKind} {left right : RuntimeCtx kind}

/-- Joining a context without borrowed cells retains exactly the actual right observation. -/
theorem readBorrowedClassical_join_right (separate : RuntimeCtx.StorageDisjoint left right)
    (empty : left.borrowedClassicalCells = []) (first : Store left) (second : Store right) :
    HEq (join separate first second).readBorrowedClassical second.readBorrowedClassical :=
  readBorrowedCells_join_of_empty left.entries right.entries first.cells second.cells empty

/-- Splitting the real store exposes its entire borrowed observation in the right frame. -/
theorem readBorrowedClassical_split_right (separate : RuntimeCtx.StorageDisjoint left right)
    (empty : left.borrowedClassicalCells = [])
    (store : Store (left.disjointUnion right separate)) :
    HEq store.readBorrowedClassical (split separate store).2.readBorrowedClassical := by
  have same := readBorrowedClassical_join_right separate empty
    (split separate store).1 (split separate store).2
  rw [join_split_store] at same
  exact same

end QuantumAlg.Execution.ContextUnion
