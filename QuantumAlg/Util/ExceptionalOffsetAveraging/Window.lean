/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.ExceptionalOffsetAveraging
import all QuantumAlg.Util.Nat.FixedWidth.Radix
import Mathlib.Data.List.OfFn

/-!
# Branch-dependent unsigned window addends on the complete exponent square

Both actual base points are parameters. In particular, this interface does
not silently negate the second classical input port. The zero address is
an unselected identity step in the same branch family and offset average.
-/

namespace QuantumAlg.ExceptionalOffsetAveraging.Window

noncomputable section

variable {G : Type*} [Group G]

/-- The unsigned runtime address attached to each original stream and window position. -/
def address (radix windows : Nat) (branch : Nat × Nat) (position : Fin (windows + windows)) :
    Nat :=
  if position.val < windows then Nat.FixedWidth.Radix.digit radix branch.1 position.val
  else Nat.FixedWidth.Radix.digit radix branch.2 (position.val - windows)

def selected (radix windows : Nat) (branch : Nat × Nat) (position : Fin (windows + windows)) :
    Bool := decide (address radix windows branch position ≠ 0)

/-- Every new address contributes its own branch-dependent row multiple of the actual base. -/
def addend (radix windows : Nat) (firstBase secondBase : G) (branch : Nat × Nat)
    (position : Fin (windows + windows)) : G :=
  if position.val < windows then
    firstBase ^ (radix ^ position.val * Nat.FixedWidth.Radix.digit radix branch.1 position.val)
  else
    secondBase ^ (radix ^ (position.val - windows) *
      Nat.FixedWidth.Radix.digit radix branch.2 (position.val - windows))

/-- The original zero address has exactly the identity addend in this same full family. -/
lemma addend_of_unselected (radix windows : Nat) (firstBase secondBase : G)
    (branch : Nat × Nat) (position : Fin (windows + windows))
    (inactive : selected radix windows branch position = false) :
    addend radix windows firstBase secondBase branch position = 1 := by
  have zero : address radix windows branch position = 0 := by
    simpa only [selected, decide_eq_false_iff_not, not_not] using inactive
  by_cases first : position.val < windows
  · simp only [address, first, ↓reduceIte] at zero
    simp only [addend, first, ↓reduceIte, zero, Nat.mul_zero, pow_zero]
  · simp only [address, first, ↓reduceIte] at zero
    simp only [addend, first, ↓reduceIte, zero, Nat.mul_zero, pow_zero]

private lemma remove_inactive {Branch : Type*} (steps : Nat)
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

private lemma window_powers (radix value windows : Nat) (base initial : G) :
    (List.finRange windows).foldl
        (fun product index => product * base ^
          (radix ^ index.val * Nat.FixedWidth.Radix.digit radix value index.val)) initial =
      initial * base ^ (value % radix ^ windows) := by
  have weights : ((List.finRange windows).map (fun index =>
      radix ^ index.val * Nat.FixedWidth.Radix.digit radix value index.val)).sum =
        Nat.FixedWidth.Radix.prefixValue radix value windows := by
    rw [← Fin.sum_univ_def]
    exact Nat.FixedWidth.Radix.sum_digits radix value windows
  exact (foldl_mul_powers (List.finRange windows) base initial _).trans
    (congrArg (fun amount => initial * base ^ amount)
      (weights.trans (Nat.FixedWidth.Radix.prefix_eq_mod radix value windows)))

private lemma finRange_add (first second : Nat) :
    List.finRange (first + second) =
      (List.finRange first).map (Fin.castAdd second) ++
        (List.finRange second).map (Fin.natAdd first) := by
  simp only [List.finRange, List.map_ofFn, List.ofFn_add]
  rfl

/-- The exact complete two-stream window family yields the two original exponent powers. -/
lemma prefixMultiplier_complete (radix windows : Nat) (firstBase secondBase : G)
    (branch : Nat × Nat) :
    prefixMultiplier (windows + windows) (selected radix windows)
        (addend radix windows firstBase secondBase branch) branch (windows + windows) =
      firstBase ^ (branch.1 % radix ^ windows) * secondBase ^ (branch.2 % radix ^ windows) := by
  rw [remove_inactive _ _ _ _
    (addend_of_unselected radix windows firstBase secondBase branch), finRange_add,
    List.foldl_append, List.foldl_map, List.foldl_map]
  have firstUpdate : (fun product (index : Fin windows) =>
      product * addend radix windows firstBase secondBase branch (index.castAdd windows)) =
      (fun product index => product * firstBase ^
        (radix ^ index.val * Nat.FixedWidth.Radix.digit radix branch.1 index.val)) := by
    funext product index
    simp only [addend, Fin.val_castAdd, index.isLt, ↓reduceIte]
  have secondUpdate : (fun product (index : Fin windows) =>
      product * addend radix windows firstBase secondBase branch (index.natAdd windows)) =
      (fun product index => product * secondBase ^
        (radix ^ index.val * Nat.FixedWidth.Radix.digit radix branch.2 index.val)) := by
    funext product index
    simp only [addend, Fin.val_natAdd]
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [firstUpdate, secondUpdate, window_powers, window_powers, one_mul]

/-- The same full family on an original branch carrier retains its exact source values. -/
lemma prefixMultiplier_complete_mapped {Branch : Type*}
    (radix windows : Nat) (firstBase secondBase : G)
    (values : Branch → Nat × Nat) (branch : Branch) :
    prefixMultiplier (windows + windows) (fun original => selected radix windows (values original))
        (addend radix windows firstBase secondBase (values branch)) branch (windows + windows) =
      firstBase ^ ((values branch).1 % radix ^ windows) *
        secondBase ^ ((values branch).2 % radix ^ windows) :=
  prefixMultiplier_complete radix windows firstBase secondBase (values branch)

end

end QuantumAlg.ExceptionalOffsetAveraging.Window
