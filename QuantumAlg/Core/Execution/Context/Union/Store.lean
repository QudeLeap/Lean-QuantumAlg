/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.References
import all QuantumAlg.Core.Execution.Store.Ext

/-!
# Exact classical storage of an actual context union

The heterogeneous cells of the appended entries are precisely the two
original stores. Their structural product correspondence retains quantum
presence markers and every finite classical value. It neither allocates
storage nor removes any classical correlation with the quantum state.
-/

namespace QuantumAlg.Execution.ContextUnion

private def joinCells {kind : ProblemKind} :
    (left right : List (RuntimeEntry kind)) → Cells left → Cells right → Cells (left ++ right)
  | [], _, _, second => second
  | _ :: tail, right, first, second => (first.1, joinCells tail right first.2 second)

private def splitCells {kind : ProblemKind} :
    (left right : List (RuntimeEntry kind)) → Cells (left ++ right) → Cells left × Cells right
  | [], _, cells => ((), cells)
  | _ :: tail, right, cells =>
      let rest := splitCells tail right cells.2
      ((cells.1, rest.1), rest.2)

private lemma split_join {kind : ProblemKind} (left right : List (RuntimeEntry kind))
    (first : Cells left) (second : Cells right) :
    splitCells left right (joinCells left right first second) = (first, second) := by
  induction left with
  | nil => cases first; rfl
  | cons head tail ih =>
      obtain ⟨value, first⟩ := first
      simp only [joinCells, splitCells, ih]

private lemma join_split {kind : ProblemKind} (left right : List (RuntimeEntry kind))
    (cells : Cells (left ++ right)) :
    joinCells left right (splitCells left right cells).1 (splitCells left right cells).2 =
      cells := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      obtain ⟨value, rest⟩ := cells
      exact congrArg (Prod.mk value) (ih rest)

variable {kind : ProblemKind} {left right : RuntimeCtx kind}
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- Join exactly the actual cells of the two disjoint runtime contexts. -/
def join (first : Store left) (second : Store right) :
    Store (left.disjointUnion right separate) :=
  ⟨joinCells left.entries right.entries first.cells second.cells⟩

/-- Split the actual appended cell list into its original two stores. -/
def split (store : Store (left.disjointUnion right separate)) : Store left × Store right :=
  let cells := splitCells left.entries right.entries store.cells
  (⟨cells.1⟩, ⟨cells.2⟩)

/-- Joining stores preserves both complete original cell vectors. -/
lemma split_join_store (first : Store left) (second : Store right) :
    split separate (join separate first second) = (first, second) := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  have actual := split_join left.entries right.entries first second
  exact congrArg (fun values : Cells left.entries × Cells right.entries =>
    ((⟨values.1⟩ : Store left), (⟨values.2⟩ : Store right))) actual

/-- Splitting loses no classical value or quantum presence marker. -/
lemma join_split_store (store : Store (left.disjointUnion right separate)) :
    join separate (split separate store).1 (split separate store).2 = store := by
  obtain ⟨cells⟩ := store
  exact congrArg Store.mk (join_split left.entries right.entries cells)

/-- Exact actual-store product correspondence, independent of state or probability. -/
def storeEquiv : Store (left.disjointUnion right separate) ≃ (Store left × Store right) where
  toFun := split separate
  invFun stores := join separate stores.1 stores.2
  left_inv := join_split_store separate
  right_inv stores := split_join_store separate stores.1 stores.2

end QuantumAlg.Execution.ContextUnion
