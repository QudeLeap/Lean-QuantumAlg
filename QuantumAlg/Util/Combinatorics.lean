/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite combinatorial enumerations

Small, quantum-free enumerators shared by closed classical post-processing
programs. Each unordered pair occurs exactly once and in source-list order.
-/

section

namespace List

variable {α : Type*}

/-- Enumerate all two-element index subsets of a list, preserving the order of
the two selected entries. -/
def unorderedPairs : List α → List (α × α)
  | [] => []
  | head :: tail => tail.map (head, ·) ++ unorderedPairs tail

@[simp] theorem unorderedPairs_nil : unorderedPairs ([] : List α) = [] := rfl

@[simp] theorem unorderedPairs_cons (head : α) (tail : List α) :
    unorderedPairs (head :: tail) =
      tail.map (head, ·) ++ unorderedPairs tail :=
  rfl

/-- The enumerator contains exactly one entry for every two-element subset. -/
theorem length_unorderedPairs (values : List α) :
    values.unorderedPairs.length = values.length.choose 2 := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [unorderedPairs, ih, Nat.choose_succ_succ,
        Nat.choose_one_right]

/-- Mapping values before pair enumeration is the same as mapping both
components of every canonical unordered pair. -/
theorem unorderedPairs_map {β : Type*} (values : List α) (f : α → β) :
    (values.map f).unorderedPairs =
      values.unorderedPairs.map fun pair => (f pair.1, f pair.2) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [unorderedPairs, ih, List.map_append, List.map_map]

end List

namespace List.Vector

variable {α : Type*} {n : Nat}

/-- Enumerate every unordered pair of a fixed-length vector.  The result type
records the exact binomial number of pairs, so execution semantics cannot be
paired with an independently supplied batch size. -/
def unorderedPairs (values : List.Vector α n) :
    List.Vector (α × α) (n.choose 2) :=
  ⟨values.toList.unorderedPairs, by
    simpa using List.length_unorderedPairs values.toList⟩

/-- Forgetting the length index recovers the canonical list enumerator. -/
@[simp] theorem toList_unorderedPairs (values : List.Vector α n) :
    values.unorderedPairs.toList = values.toList.unorderedPairs :=
  rfl

/-- The fixed-length enumerator preserves the list-level map/pair law. -/
theorem toList_unorderedPairs_map {β : Type*}
    (values : List.Vector α n) (f : α → β) :
    (values.map f).unorderedPairs.toList =
      values.unorderedPairs.toList.map fun pair => (f pair.1, f pair.2) := by
  simp [List.unorderedPairs_map]

end List.Vector

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Exact count of fixed-length words whose every coordinate lies in a finite
set. -/
theorem card_filter_pi_forall_mem (s : Finset α) (n : Nat) :
    ((Finset.univ : Finset (Fin n → α)).filter fun words =>
      ∀ index, words index ∈ s).card = s.card ^ n := by
  have heq :
      ((Finset.univ : Finset (Fin n → α)).filter fun words =>
          ∀ index, words index ∈ s) =
        Fintype.piFinset fun _ : Fin n => s := by
    ext words
    simp [Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset_const]

/-- Union bound for fixed-length words with at least one coordinate in a
finite exceptional set. -/
theorem card_filter_pi_exists_mem_le (s : Finset α) (n : Nat) :
    ((Finset.univ : Finset (Fin n → α)).filter fun words =>
      ∃ index, words index ∈ s).card ≤
        n * s.card * Fintype.card α ^ (n - 1) := by
  classical
  let coordinateEvent (index : Fin n) : Finset (Fin n → α) :=
    Finset.univ.filter fun words => words index ∈ s
  let valueFiber (index : Fin n) (value : α) : Finset (Fin n → α) :=
    Finset.univ.filter fun words => words index = value
  have hcoordinate (index : Fin n) :
      (coordinateEvent index).card ≤
        s.card * Fintype.card α ^ (n - 1) := by
    have hsubset : coordinateEvent index ⊆
        s.biUnion (valueFiber index) := by
      intro words hwords
      have hmem : words index ∈ s :=
        (Finset.mem_filter.mp hwords).2
      exact Finset.mem_biUnion.mpr ⟨words index, hmem,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    calc
      (coordinateEvent index).card ≤
          (s.biUnion (valueFiber index)).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ value ∈ s, (valueFiber index value).card :=
        Finset.card_biUnion_le
      _ = ∑ _value ∈ s, Fintype.card α ^ (n - 1) := by
        apply Finset.sum_congr rfl
        intro value _hvalue
        change ((Finset.univ : Finset (Fin n → α)).filter fun words =>
          words index = value).card = _
        rw [← Fintype.piFinset_univ]
        simpa using Fintype.card_filter_piFinset_const_eq_of_mem
          (Finset.univ : Finset α) index (Finset.mem_univ value)
      _ = s.card * Fintype.card α ^ (n - 1) := by simp
  have hsubset :
      ((Finset.univ : Finset (Fin n → α)).filter fun words =>
        ∃ index, words index ∈ s) ⊆
        (Finset.univ : Finset (Fin n)).biUnion coordinateEvent := by
    intro words hwords
    rcases (Finset.mem_filter.mp hwords).2 with ⟨index, hindex⟩
    exact Finset.mem_biUnion.mpr ⟨index, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hindex⟩⟩
  calc
    ((Finset.univ : Finset (Fin n → α)).filter fun words =>
        ∃ index, words index ∈ s).card ≤
        ((Finset.univ : Finset (Fin n)).biUnion coordinateEvent).card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ index : Fin n, (coordinateEvent index).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _index : Fin n,
        s.card * Fintype.card α ^ (n - 1) :=
      _root_.Finset.sum_le_sum fun index _ => hcoordinate index
    _ = n * s.card * Fintype.card α ^ (n - 1) := by
      simp [Nat.mul_assoc]

end Finset

end
