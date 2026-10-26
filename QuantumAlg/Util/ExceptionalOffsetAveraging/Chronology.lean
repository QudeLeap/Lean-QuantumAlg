/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.ExceptionalOffsetAveraging.Window
import all QuantumAlg.Util.Nat.FixedWidth.Window.Chronology

/-!
# Complete high-to-low window products in their original two-stream order

Only powers of the same group element are reordered inside each stream.
The two streams are never exchanged, so the ambient group need not commute.
This is a group multiplier law, not commutation of measured circuit operators.
-/

namespace QuantumAlg.ExceptionalOffsetAveraging.Chronology

noncomputable section

variable {G : Type*} [Group G]

open Nat.FixedWidth.Window.Chronology

/-- A complete power word is invariant under an arbitrary permutation of its own positions. -/
lemma foldl_powers_reindexed (count : Nat) (order : Equiv.Perm (Fin count))
    (base initial : G) (weight : Fin count → Nat) :
    (List.finRange count).foldl (fun product index => product * base ^ weight (order index))
        initial =
      (List.finRange count).foldl (fun product index => product * base ^ weight index) initial := by
  rw [foldl_mul_powers, foldl_mul_powers, ← Fin.sum_univ_def, ← Fin.sum_univ_def]
  exact congrArg (fun amount => initial * base ^ amount) (Equiv.sum_comp order weight)

private lemma complete_unselected {Branch : Type*} (steps : Nat)
    (selected : Branch → Fin steps → Bool) (addend : Fin steps → G) (branch : Branch)
    (identity : ∀ index, selected branch index = false → addend index = 1) :
    prefixMultiplier steps selected addend branch steps =
      (List.finRange steps).foldl (fun product index => product * addend index) 1 := by
  have update : (fun product index =>
      if selected branch index = true then product * addend index else product) =
      (fun product index => product * addend index) := by
    funext product index
    cases bit : selected branch index with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, identity index bit, mul_one]
    | true => rfl
  rw [prefixMultiplier, List.take_of_length_le (by simp only [List.length_finRange, le_refl]),
    update]

/-- Reversing the windows inside each stream preserves the completed ordered product. -/
lemma windowPrefix_complete (radix windows : Nat) (firstBase secondBase : G)
    (branch : Nat × Nat) :
    prefixMultiplier (windows + windows)
        (fun original index => Window.selected radix windows original (paired windows index))
        (fun index => Window.addend radix windows firstBase secondBase branch
          (paired windows index)) branch (windows + windows) =
      firstBase ^ (branch.1 % radix ^ windows) * secondBase ^ (branch.2 % radix ^ windows) := by
  rw [complete_unselected _ _ _ _ (fun index inactive =>
    Window.addend_of_unselected radix windows firstBase secondBase branch
      (paired windows index) inactive), Window.finRange_add,
    List.foldl_append, List.foldl_map, List.foldl_map]
  have firstUpdate : (fun product (index : Fin windows) =>
      product * Window.addend radix windows firstBase secondBase branch
        (paired windows (index.castAdd windows))) =
      (fun product index => product * firstBase ^
        (radix ^ (logical windows index).val *
          Nat.FixedWidth.Radix.digit radix branch.1 (logical windows index).val)) := by
    funext product index
    simp only [paired_first, Window.addend, Fin.val_castAdd,
      (logical windows index).isLt, ↓reduceIte]
  have secondUpdate : (fun product (index : Fin windows) =>
      product * Window.addend radix windows firstBase secondBase branch
        (paired windows (index.natAdd windows))) =
      (fun product index => product * secondBase ^
        (radix ^ (logical windows index).val *
          Nat.FixedWidth.Radix.digit radix branch.2 (logical windows index).val)) := by
    funext product index
    simp only [paired_second, Window.addend, Fin.val_natAdd]
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [firstUpdate, secondUpdate]
  rw [foldl_powers_reindexed windows (logical windows) secondBase _
    (fun index => radix ^ index.val * Nat.FixedWidth.Radix.digit radix branch.2 index.val)]
  rw [foldl_powers_reindexed windows (logical windows) firstBase 1
    (fun index => radix ^ index.val * Nat.FixedWidth.Radix.digit radix branch.1 index.val)]
  rw [Window.window_powers, Window.window_powers, one_mul]

end

end QuantumAlg.ExceptionalOffsetAveraging.Chronology
