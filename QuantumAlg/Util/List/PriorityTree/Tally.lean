/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.List.PriorityTree.Balanced
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range

/-!
# Scalar balanced-tree tallies before concrete finite-index specialization

The recurrence follows complete consecutive source intervals. It permits
closed native-coordinate evaluation without unfolding a long finite list
and a circuit interpreter at the same time.
-/

namespace QuantumAlg.ListPriority.Tree

variable {Label : Type*}

/-- A scalar leaf charge and complete higher-subword charge at every original fork. -/
def tally (leaf : Label → Nat) (fork : Nat → Nat) : Tree Label → Nat
  | .empty => 0
  | .leaf label => leaf label
  | .fork higher lower => tally leaf fork higher + tally leaf fork lower + fork higher.leaves.length

/-- Independent logarithmic-depth scalar recurrence on the original consecutive numeric interval. -/
def balancedTally (leaf fork : Nat → Nat) : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | _, start, 1 => leaf start
  | 0, start, _ + 2 => leaf start
  | height + 1, start, size + 2 =>
      let length := size + 2
      let higher := (length + 1) / 2
      balancedTally leaf fork height start higher +
        balancedTally leaf fork height (start + higher) (length - higher) + fork higher

/-- Ordered consecutive original leaves have exactly the independent scalar balanced recurrence. -/
lemma balanced_tally (address : Label → Nat) (leaf fork : Nat → Nat) (height : Nat)
    (labels : List Label) (start : Nat)
    (ordered : labels.map address = List.range' start labels.length)
    (capacity : labels.length ≤ 2 ^ height) :
    tally (fun label => leaf (address label)) fork (balanced height labels) =
      balancedTally leaf fork height start labels.length := by
  induction height generalizing labels start with
  | zero =>
      cases labels with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              have firstValue : address first = start := by
                simpa only [List.map_cons, List.map_nil, List.length_singleton,
                  List.range'_succ, List.range'_zero, List.cons.injEq, and_true] using ordered
              simp only [balanced, tally, List.length_singleton, balancedTally, firstValue]
          | cons second rest =>
              simp only [List.length_cons, Nat.pow_zero] at capacity
              omega
  | succ height ih =>
      cases labels with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              have firstValue : address first = start := by
                simpa only [List.map_cons, List.map_nil, List.length_singleton,
                  List.range'_succ, List.range'_zero, List.cons.injEq, and_true] using ordered
              simp only [balanced, tally, List.length_singleton, balancedTally, firstValue]
          | cons second rest =>
              let labels := first :: second :: rest
              let cut := (labels.length + 1) / 2
              have cutFits : cut ≤ labels.length := by
                dsimp only [cut, labels]
                simp only [List.length_cons]
                omega
              have capacity' : labels.length ≤ 2 ^ height * 2 := by
                simpa only [Nat.pow_succ] using capacity
              have higherFits : (labels.take cut).length ≤ 2 ^ height := by
                rw [List.length_take, Nat.min_eq_left cutFits]
                dsimp only [cut]
                omega
              have lowerFits : (labels.drop cut).length ≤ 2 ^ height := by
                rw [List.length_drop]
                dsimp only [cut]
                omega
              have higherOrder : (labels.take cut).map address =
                  List.range' start (labels.take cut).length := by
                rw [List.map_take, ordered, List.take_range'_of_length_ge cutFits,
                  List.length_take, Nat.min_eq_left cutFits]
              have lowerOrder : (labels.drop cut).map address =
                  List.range' (start + cut) (labels.drop cut).length := by
                rw [List.map_drop, ordered, List.drop_range', List.length_drop, Nat.mul_one]
              have high := ih (labels.take cut) start higherOrder higherFits
              have low := ih (labels.drop cut) (start + cut) lowerOrder lowerFits
              have complete := balanced_leaves height (labels.take cut) higherFits
              change tally _ _ (.fork (balanced height (labels.take cut))
                  (balanced height (labels.drop cut))) = _
              rw [tally, high, low, complete, List.length_take, Nat.min_eq_left cutFits,
                List.length_drop]
              rfl

/-- Original finite labels have their complete numeric order
without any literal unfolding. -/
lemma finRange_address_order (count : Nat) :
    (List.finRange count).map Fin.val = List.range' 0 count := by
  apply List.ext_getElem <;> simp

end QuantumAlg.ListPriority.Tree
