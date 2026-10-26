/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.PriorityTree
import Mathlib.Data.List.FinRange

/-!
# The independent first marked numeric position with the full length sentinel

The public order is exactly the original finite index order. This pure
specification records no executed search or allocation.
-/

namespace QuantumAlg.ListPriority.Tree

variable {count : Nat}

/-- The first marked original index, with the original count as the all-zero sentinel. -/
def position (marked : Fin count → Bool) : Nat :=
  (List.finRange count).findIdx marked

/-- The sentinel bounds the independent finite-list search. -/
lemma position_le (marked : Fin count → Bool) : position marked ≤ count := by
  simpa only [position, List.length_finRange] using
    List.findIdx_le_length (xs := List.finRange count) (p := marked)

/-- Every original source position earlier than the answer is false. -/
lemma before_position (marked : Fin count → Bool) (index : Fin count)
    (earlier : index.val < position marked) : marked index = false := by
  have absent := List.not_of_lt_findIdx (xs := List.finRange count) (p := marked) earlier
  simpa only [List.getElem_finRange, Fin.cast_mk] using absent

/-- Every nonsentinel answer is an actual marked original source position. -/
lemma at_position (marked : Fin count → Bool) (present : position marked < count) :
    marked ⟨position marked, present⟩ = true := by
  have selected := List.findIdx_getElem (xs := List.finRange count) (p := marked)
    (w := by simpa only [position, List.length_finRange] using present)
  simpa only [position, List.getElem_finRange, Fin.cast_mk] using selected

/-- The ordered tree returns exactly the bounded numeric answer or the full-length sentinel. -/
lemma first_eq_position (tree : ListPriority.Tree (Fin count))
    (ordered : tree.leaves = List.finRange count) (marked : Fin count → Bool) :
    tree.first marked = if present : position marked < count then
      some ⟨position marked, present⟩ else none := by
  rw [first_eq_find, ordered, List.find?_eq_getElem?_findIdx]
  by_cases present : position marked < count
  · rw [dif_pos present, List.getElem?_eq_getElem
      (by simpa only [position, List.length_finRange] using present)]
    simp only [position, List.getElem_finRange, Fin.cast_mk]
  · rw [dif_neg present, List.getElem?_eq_none]
    simpa only [position, List.length_finRange] using Nat.le_of_not_gt present

end QuantumAlg.ListPriority.Tree
