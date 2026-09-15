/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.FinPow
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite averaging for exceptional group offsets

This module isolates the quantum-free counting argument behind randomized
accumulator offsets.  A branch executes a finite sequence of selected group
multiplications.  At each step there are at most two initial offsets for which
the pre-step accumulator equals the addend or its inverse.  Double-counting the
finite offset/branch incidence relation therefore selects one fixed offset
whose exceptional branch fraction is no larger than the average bound.
-/

section

namespace QuantumAlg
namespace ExceptionalOffsetAveraging

noncomputable section

variable {G Branch : Type*} [Group G]

private theorem natOfBits_eq_weightedSum {width : Nat}
    (bits : Fin width → Bool) :
    Nat.ofBits bits =
      ∑ bit : Fin width, (bits bit).toNat * 2 ^ bit.val := by
  induction width with
  | zero => simp
  | succ width induction =>
      rw [Nat.ofBits_succ, Fin.sum_univ_succ]
      rw [induction (bits ∘ Fin.succ)]
      simp only [Function.comp_apply, Fin.val_zero, pow_zero, mul_one,
        Fin.val_succ]
      have shifted :
          (∑ bit : Fin width,
              (bits bit.succ).toNat * 2 ^ (bit.val + 1)) =
            2 * ∑ bit : Fin width,
              (bits bit.succ).toNat * 2 ^ bit.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro bit _
        rw [pow_succ]
        ring
      rw [shifted]
      omega

private theorem foldl_mul_powers {Index : Type*}
    (indices : List Index) (base initial : G) (weight : Index → Nat) :
    indices.foldl (fun product index => product * base ^ weight index) initial =
      initial * base ^ (indices.map weight).sum := by
  induction indices generalizing initial with
  | nil => simp
  | cons index rest induction =>
      rw [List.foldl_cons, induction]
      simp only [List.map_cons, List.sum_cons, pow_add]
      simp [mul_assoc]

/-- Reading all physical bits from most significant to least significant and
right-multiplying the corresponding powers produces the represented natural
power.  The initial accumulator is preserved on the left. -/
theorem foldl_bigEndianPowers (width : Nat) (base initial : G)
    (value : Fin (2 ^ width)) :
    (List.finRange width).foldl
        (fun product position =>
          if value.val.testBit (width - 1 - position.val) = true then
            product * base ^ (2 ^ (width - 1 - position.val))
          else product)
        initial =
      initial * base ^ value.val := by
  let weight : Fin width → Nat := fun position =>
    (value.val.testBit (width - 1 - position.val)).toNat *
      2 ^ (width - 1 - position.val)
  have updateEquality :
      (fun product position =>
          if value.val.testBit (width - 1 - position.val) = true then
            product * base ^ (2 ^ (width - 1 - position.val))
          else product) =
        (fun product position => product * base ^ weight position) := by
    funext product position
    unfold weight
    cases value.val.testBit (width - 1 - position.val) <;> simp
  rw [updateEquality, foldl_mul_powers]
  congr 2
  rw [← Fin.sum_univ_def]
  simp only [weight]
  have reverseIndex (position : Fin width) :
      width - 1 - position.val = (Fin.rev position).val := by
    change width - 1 - position.val = width - (position.val + 1)
    rw [Nat.sub_sub]
    simp only [Nat.add_comm]
  apply Eq.trans (Finset.sum_congr rfl fun position _ => by
    rw [reverseIndex position])
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin width))]
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  rw [← natOfBits_eq_weightedSum]
  simpa only [Nat.mod_eq_of_lt value.isLt] using
    (Nat.ofBits_testBit value.val width)

/-- Group multiplier accumulated before the first `processed` scheduled
steps.  Unselected steps contribute the identity. -/
def prefixMultiplier (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (processed : Nat) : G :=
  ((List.finRange stepCount).take processed).foldl
    (fun product step =>
      if selected branch step = true then product * addend step else product)
    1

private theorem finRange_take_succ {count : Nat} (step : Fin count) :
    (List.finRange count).take (step.val + 1) =
      (List.finRange count).take step.val ++ [step] := by
  have indexLt : step.val < (List.finRange count).length := by
    simpa only [List.length_finRange] using step.isLt
  have atIndex : (List.finRange count)[step.val]'indexLt = step := by
    simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]
  simpa only [atIndex] using
    (List.take_concat_get' (List.finRange count) step.val indexLt).symm

/-- Extending a valid prefix by one step multiplies by exactly that step's
addend when it is selected. -/
theorem prefixMultiplier_succ (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (processed : Nat) (processedLt : processed < stepCount) :
    prefixMultiplier stepCount selected addend branch (processed + 1) =
      if selected branch ⟨processed, processedLt⟩ = true then
        prefixMultiplier stepCount selected addend branch processed *
          addend ⟨processed, processedLt⟩
      else
        prefixMultiplier stepCount selected addend branch processed := by
  unfold prefixMultiplier
  rw [finRange_take_succ ⟨processed, processedLt⟩, List.foldl_append]
  rfl

/-- Physical control selection for two consecutive big-endian exponent
registers. -/
def pairedBigEndianSelected (width : Nat)
    (branch : Fin (2 ^ width) × Fin (2 ^ width))
    (position : Fin (2 * width)) : Bool :=
  if _first : position.val < width then
    branch.1.val.testBit (width - 1 - position.val)
  else
    branch.2.val.testBit (width - 1 - (position.val - width))

/-- Fixed group addend attached to each physical position of two consecutive
big-endian exponent registers. -/
def pairedBigEndianAddend (width : Nat) (leftBase rightBase : G)
    (position : Fin (2 * width)) : G :=
  if _first : position.val < width then
    leftBase ^ (2 ^ (width - 1 - position.val))
  else
    (rightBase ^ (2 ^ (width - 1 - (position.val - width))))⁻¹

/-- The complete two-register schedule implements
`leftBase^a * (rightBase^b)⁻¹` exactly. -/
theorem prefixMultiplier_pairedBigEndian (width : Nat)
    (leftBase rightBase : G)
    (branch : Fin (2 ^ width) × Fin (2 ^ width)) :
    prefixMultiplier (2 * width) (pairedBigEndianSelected width)
        (pairedBigEndianAddend width leftBase rightBase)
        branch (2 * width) =
      leftBase ^ branch.1.val * (rightBase ^ branch.2.val)⁻¹ := by
  let leftUpdate : G → Fin width → G := fun product position =>
    if branch.1.val.testBit (width - 1 - position.val) = true then
      product * leftBase ^ (2 ^ (width - 1 - position.val))
    else product
  have leftPrefix : ∀ processed : Nat, processed ≤ width →
      prefixMultiplier (2 * width) (pairedBigEndianSelected width)
          (pairedBigEndianAddend width leftBase rightBase)
          branch processed =
        ((List.finRange width).take processed).foldl leftUpdate 1 := by
    intro processed processedLe
    induction processed with
    | zero => rfl
    | succ processed induction =>
        have processedLt : processed < width := Nat.lt_of_succ_le processedLe
        have globalLt : processed < 2 * width := by omega
        have previous := induction (Nat.le_of_lt processedLt)
        rw [prefixMultiplier_succ (G := G)
          (2 * width) (pairedBigEndianSelected width)
          (pairedBigEndianAddend width leftBase rightBase)
          branch processed globalLt]
        rw [finRange_take_succ (⟨processed, processedLt⟩ : Fin width),
          List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← previous]
        simp only [pairedBigEndianSelected, pairedBigEndianAddend, leftUpdate]
        rw [dif_pos processedLt, dif_pos processedLt]
  have takeLeft : (List.finRange width).take width = List.finRange width := by
    simpa only [List.length_finRange] using
      (List.take_length (l := List.finRange width))
  have leftComplete :
      prefixMultiplier (2 * width) (pairedBigEndianSelected width)
          (pairedBigEndianAddend width leftBase rightBase)
          branch width = leftBase ^ branch.1.val := by
    rw [leftPrefix width (Nat.le_refl _), takeLeft]
    exact foldl_bigEndianPowers width leftBase 1 branch.1 |>.trans (by simp)
  let rightUpdate : G → Fin width → G := fun product position =>
    if branch.2.val.testBit (width - 1 - position.val) = true then
      product * rightBase⁻¹ ^ (2 ^ (width - 1 - position.val))
    else product
  have rightPrefix : ∀ processed : Nat, processed ≤ width →
      prefixMultiplier (2 * width) (pairedBigEndianSelected width)
          (pairedBigEndianAddend width leftBase rightBase)
          branch (width + processed) =
        ((List.finRange width).take processed).foldl rightUpdate
          (leftBase ^ branch.1.val) := by
    intro processed processedLe
    induction processed with
    | zero =>
        simpa only [Nat.add_zero, List.take_zero, List.foldl_nil] using
          leftComplete
    | succ processed induction =>
        have processedLt : processed < width := Nat.lt_of_succ_le processedLe
        have globalLt : width + processed < 2 * width := by omega
        have previous := induction (Nat.le_of_lt processedLt)
        rw [show width + (processed + 1) = (width + processed) + 1 by omega]
        rw [prefixMultiplier_succ (G := G)
          (2 * width) (pairedBigEndianSelected width)
          (pairedBigEndianAddend width leftBase rightBase)
          branch (width + processed) globalLt]
        rw [finRange_take_succ (⟨processed, processedLt⟩ : Fin width),
          List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil]
        rw [← previous]
        have notFirst : ¬ width + processed < width := by omega
        have subtractWidth : width + processed - width = processed := by omega
        simp only [pairedBigEndianSelected, pairedBigEndianAddend, rightUpdate]
        rw [dif_neg notFirst, dif_neg notFirst, subtractWidth]
        rw [inv_pow]
  have takeRight : (List.finRange width).take width = List.finRange width :=
    takeLeft
  have complete := rightPrefix width (Nat.le_refl _)
  rw [takeRight, foldl_bigEndianPowers] at complete
  simpa only [two_mul, inv_pow] using complete

/-- An initial offset is admissible for a branch when every selected step
avoids the two exceptional pre-step accumulator values. -/
def Admissible (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (offset : G) (branch : Branch) : Prop :=
  ∀ step : Fin stepCount, selected branch step = true →
    offset * prefixMultiplier stepCount selected addend branch step.val ≠
        addend step ∧
      offset * prefixMultiplier stepCount selected addend branch step.val ≠
        (addend step)⁻¹

private def badAt (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (step : Fin stepCount) : Finset G := by
  classical
  exact offsets.filter fun offset =>
    selected branch step = true ∧
      (offset * prefixMultiplier stepCount selected addend branch step.val =
          addend step ∨
        offset * prefixMultiplier stepCount selected addend branch step.val =
          (addend step)⁻¹)

private def rightFiber (offsets : Finset G) (factor target : G) : Finset G := by
  classical
  exact offsets.filter fun offset => offset * factor = target

private theorem filter_mul_right_eq_card_le_one
    (offsets : Finset G) (factor target : G) :
    (rightFiber offsets factor target).card ≤ 1 := by
  classical
  rw [Finset.card_le_one_iff]
  intro left right leftMember rightMember
  simp only [rightFiber, Finset.mem_filter] at leftMember rightMember
  exact mul_right_cancel (leftMember.2.trans rightMember.2.symm)

private theorem badAt_card_le_two (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (step : Fin stepCount) :
    (badAt offsets stepCount selected addend branch step).card ≤ 2 := by
  classical
  let factor := prefixMultiplier stepCount selected addend branch step.val
  let same := rightFiber offsets factor (addend step)
  let inverse := rightFiber offsets factor (addend step)⁻¹
  have subset : badAt offsets stepCount selected addend branch step ⊆
      same ∪ inverse := by
    intro offset member
    simp only [badAt, Finset.mem_filter] at member
    simp only [same, inverse, rightFiber, Finset.mem_union, Finset.mem_filter]
    rcases member.2.2 with equality | equality
    · exact Or.inl ⟨member.1, equality⟩
    · exact Or.inr ⟨member.1, equality⟩
  calc
    (badAt offsets stepCount selected addend branch step).card ≤
        (same ∪ inverse).card := Finset.card_le_card subset
    _ ≤ same.card + inverse.card := Finset.card_union_le same inverse
    _ ≤ 1 + 1 := Nat.add_le_add
      (filter_mul_right_eq_card_le_one offsets factor (addend step))
      (filter_mul_right_eq_card_le_one offsets factor (addend step)⁻¹)
    _ = 2 := by omega

/-- Candidate offsets that are exceptional for one branch. -/
def badOffsets (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch) : Finset G := by
  classical
  exact offsets.filter fun offset =>
    ¬ Admissible stepCount selected addend offset branch

/-- Every branch excludes at most two offsets per scheduled step. -/
theorem badOffsets_card_le_two_mul (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch) :
    (badOffsets offsets stepCount selected addend branch).card ≤
      2 * stepCount := by
  classical
  have subset : badOffsets offsets stepCount selected addend branch ⊆
      (Finset.univ : Finset (Fin stepCount)).biUnion
        (badAt offsets stepCount selected addend branch) := by
    intro offset member
    simp only [badOffsets, Finset.mem_filter] at member
    have exceptional : ∃ step : Fin stepCount,
        selected branch step = true ∧
          (offset * prefixMultiplier stepCount selected addend branch step.val =
              addend step ∨
            offset * prefixMultiplier stepCount selected addend branch step.val =
              (addend step)⁻¹) := by
      unfold Admissible at member
      push Not at member
      obtain ⟨step, active, exceptional⟩ := member.2
      refine ⟨step, active, ?_⟩
      by_cases same :
          offset * prefixMultiplier stepCount selected addend branch step.val =
            addend step
      · exact Or.inl same
      · exact Or.inr (exceptional same)
    obtain ⟨step, active, bad⟩ := exceptional
    rw [Finset.mem_biUnion]
    exact ⟨step, Finset.mem_univ step, by
      simp only [badAt, Finset.mem_filter]
      exact ⟨member.1, active, bad⟩⟩
  calc
    (badOffsets offsets stepCount selected addend branch).card ≤
        ((Finset.univ : Finset (Fin stepCount)).biUnion
          (badAt offsets stepCount selected addend branch)).card :=
      Finset.card_le_card subset
    _ ≤ (Finset.univ : Finset (Fin stepCount)).card * 2 :=
      Finset.card_biUnion_le_card_mul _ _ 2 fun step _ =>
        badAt_card_le_two offsets stepCount selected addend branch step
    _ = 2 * stepCount := by simp [Nat.mul_comm]

/-- Candidate branches that are exceptional for one fixed offset. -/
def badBranches (branches : Finset Branch) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (offset : G) : Finset Branch := by
  classical
  exact branches.filter fun branch =>
    ¬ Admissible stepCount selected addend offset branch

private theorem sum_badBranches_eq_sum_badOffsets
    (offsets : Finset G) (branches : Finset Branch) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) :
    ∑ offset ∈ offsets,
        (badBranches branches stepCount selected addend offset).card =
      ∑ branch ∈ branches,
        (badOffsets offsets stepCount selected addend branch).card := by
  classical
  calc
    ∑ offset ∈ offsets,
        (badBranches branches stepCount selected addend offset).card =
        ∑ offset ∈ offsets, ∑ branch ∈ branches,
          if ¬ Admissible stepCount selected addend offset branch then 1 else 0 := by
      simp_rw [badBranches, Finset.card_filter]
    _ = ∑ branch ∈ branches, ∑ offset ∈ offsets,
          if ¬ Admissible stepCount selected addend offset branch then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ branch ∈ branches,
        (badOffsets offsets stepCount selected addend branch).card := by
      simp_rw [badOffsets, Finset.card_filter]

/-- Finite averaging selects one fixed offset whose exceptional branch count
obeys the same two-per-step average bound as uniform randomization.  The
cross-multiplied form avoids any rounding or division convention. -/
theorem exists_fixed_offset (offsets : Finset G) (branches : Finset Branch)
    (offsetsNonempty : offsets.Nonempty) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) :
    ∃ offset ∈ offsets,
      offsets.card *
          (badBranches branches stepCount selected addend offset).card ≤
        branches.card * (2 * stepCount) := by
  classical
  have totalBadBound :
      ∑ offset ∈ offsets,
          (badBranches branches stepCount selected addend offset).card ≤
        branches.card * (2 * stepCount) := by
    rw [sum_badBranches_eq_sum_badOffsets]
    calc
      ∑ branch ∈ branches,
          (badOffsets offsets stepCount selected addend branch).card ≤
          ∑ _branch ∈ branches, 2 * stepCount := by
        exact Finset.sum_le_sum fun branch _ =>
          badOffsets_card_le_two_mul offsets stepCount selected addend branch
      _ = branches.card * (2 * stepCount) := by simp
  have scaledTotal :
      ∑ offset ∈ offsets,
          offsets.card *
            (badBranches branches stepCount selected addend offset).card ≤
        ∑ _offset ∈ offsets, branches.card * (2 * stepCount) := by
    calc
      ∑ offset ∈ offsets,
          offsets.card *
            (badBranches branches stepCount selected addend offset).card =
          offsets.card *
            ∑ offset ∈ offsets,
              (badBranches branches stepCount selected addend offset).card := by
        rw [Finset.mul_sum]
      _ ≤ offsets.card * (branches.card * (2 * stepCount)) :=
        Nat.mul_le_mul_left offsets.card totalBadBound
      _ = ∑ _offset ∈ offsets, branches.card * (2 * stepCount) := by
        simp
  exact Finset.exists_le_of_sum_le offsetsNonempty scaledTotal

/-! ## Strict domain for the controlled point-addition schedule

The reversible straight-line program evaluates its first inversion even when
the external control is false, and its active branch recomputes the slope
from the output [RNSL17, ECDLP.tex:490-492,514-527].  The stricter predicate
below records the resulting denominator obligations, including the additional
active pre-step exclusion `-2Q`.  This exclusion is derived for the schedule;
Algorithm 1's caption does not state it [RNSL17, ECDLP.tex:510]. -/

/-- Explicit denominator-safe domain for Algorithm 1's inversion calls
[RNSL17, ECDLP.tex:516,525].  Every step avoids `Q` and `-Q`; an active step
additionally avoids `-2Q`. -/
def RNSLAdmissible (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (offset : G) (branch : Branch) : Prop :=
  ∀ step : Fin stepCount,
    offset * prefixMultiplier stepCount selected addend branch step.val ≠
        addend step ∧
      offset * prefixMultiplier stepCount selected addend branch step.val ≠
          (addend step)⁻¹ ∧
        (selected branch step = true →
          offset * prefixMultiplier stepCount selected addend branch step.val ≠
            (addend step * addend step)⁻¹)

private def rnslBadAt (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (step : Fin stepCount) : Finset G := by
  classical
  exact offsets.filter fun offset =>
    offset * prefixMultiplier stepCount selected addend branch step.val =
        addend step ∨
      offset * prefixMultiplier stepCount selected addend branch step.val =
        (addend step)⁻¹ ∨
      offset * prefixMultiplier stepCount selected addend branch step.val =
        (addend step * addend step)⁻¹

private theorem rnslBadAt_card_le_three
    (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch)
    (step : Fin stepCount) :
    (rnslBadAt offsets stepCount selected addend branch step).card ≤ 3 := by
  classical
  let factor := prefixMultiplier stepCount selected addend branch step.val
  let same := rightFiber offsets factor (addend step)
  let inverse := rightFiber offsets factor (addend step)⁻¹
  let twiceInverse :=
    rightFiber offsets factor (addend step * addend step)⁻¹
  have subset : rnslBadAt offsets stepCount selected addend branch step ⊆
      (same ∪ inverse) ∪ twiceInverse := by
    intro offset member
    simp only [rnslBadAt, Finset.mem_filter] at member
    simp only [same, inverse, twiceInverse, rightFiber, Finset.mem_union,
      Finset.mem_filter]
    rcases member.2 with equality | equality | equality
    · exact Or.inl (Or.inl ⟨member.1, equality⟩)
    · exact Or.inl (Or.inr ⟨member.1, equality⟩)
    · exact Or.inr ⟨member.1, equality⟩
  calc
    (rnslBadAt offsets stepCount selected addend branch step).card ≤
        ((same ∪ inverse) ∪ twiceInverse).card :=
      Finset.card_le_card subset
    _ ≤ (same ∪ inverse).card + twiceInverse.card :=
      Finset.card_union_le _ _
    _ ≤ (same.card + inverse.card) + twiceInverse.card := by
      exact Nat.add_le_add_right (Finset.card_union_le same inverse) _
    _ ≤ (1 + 1) + 1 := by
      gcongr
      · exact filter_mul_right_eq_card_le_one offsets factor (addend step)
      · exact filter_mul_right_eq_card_le_one offsets factor (addend step)⁻¹
      · exact filter_mul_right_eq_card_le_one offsets factor
          (addend step * addend step)⁻¹
    _ = 3 := by omega

/-- Candidate offsets outside the literal straight-line domain for one
branch. -/
def rnslBadOffsets (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch) : Finset G := by
  classical
  exact offsets.filter fun offset =>
    ¬ RNSLAdmissible stepCount selected addend offset branch

/-- The literal straight-line schedule excludes at most three offsets per
step. -/
theorem rnslBadOffsets_card_le_three_mul
    (offsets : Finset G) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (branch : Branch) :
    (rnslBadOffsets offsets stepCount selected addend branch).card ≤
      3 * stepCount := by
  classical
  have subset : rnslBadOffsets offsets stepCount selected addend branch ⊆
      (Finset.univ : Finset (Fin stepCount)).biUnion
        (rnslBadAt offsets stepCount selected addend branch) := by
    intro offset member
    simp only [rnslBadOffsets, Finset.mem_filter] at member
    unfold RNSLAdmissible at member
    push Not at member
    obtain ⟨step, exceptional⟩ := member.2
    rw [Finset.mem_biUnion]
    refine ⟨step, Finset.mem_univ step, ?_⟩
    simp only [rnslBadAt, Finset.mem_filter]
    refine ⟨member.1, ?_⟩
    by_cases same :
        offset * prefixMultiplier stepCount selected addend branch step.val =
          addend step
    · exact Or.inl same
    by_cases inverse :
        offset * prefixMultiplier stepCount selected addend branch step.val =
          (addend step)⁻¹
    · exact Or.inr (Or.inl inverse)
    exact Or.inr (Or.inr (exceptional same inverse).2)
  calc
    (rnslBadOffsets offsets stepCount selected addend branch).card ≤
        ((Finset.univ : Finset (Fin stepCount)).biUnion
          (rnslBadAt offsets stepCount selected addend branch)).card :=
      Finset.card_le_card subset
    _ ≤ (Finset.univ : Finset (Fin stepCount)).card * 3 :=
      Finset.card_biUnion_le_card_mul _ _ 3 fun step _ =>
        rnslBadAt_card_le_three offsets stepCount selected addend branch step
    _ = 3 * stepCount := by simp [Nat.mul_comm]

/-- Candidate branches outside the literal straight-line domain for one fixed
offset. -/
def rnslBadBranches (branches : Finset Branch) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) (offset : G) : Finset Branch := by
  classical
  exact branches.filter fun branch =>
    ¬ RNSLAdmissible stepCount selected addend offset branch

private theorem sum_rnslBadBranches_eq_sum_rnslBadOffsets
    (offsets : Finset G) (branches : Finset Branch) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) :
    ∑ offset ∈ offsets,
        (rnslBadBranches branches stepCount selected addend offset).card =
      ∑ branch ∈ branches,
        (rnslBadOffsets offsets stepCount selected addend branch).card := by
  classical
  calc
    ∑ offset ∈ offsets,
        (rnslBadBranches branches stepCount selected addend offset).card =
        ∑ offset ∈ offsets, ∑ branch ∈ branches,
          if ¬ RNSLAdmissible stepCount selected addend offset branch then
            1 else 0 := by
      simp_rw [rnslBadBranches, Finset.card_filter]
    _ = ∑ branch ∈ branches, ∑ offset ∈ offsets,
          if ¬ RNSLAdmissible stepCount selected addend offset branch then
            1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ branch ∈ branches,
        (rnslBadOffsets offsets stepCount selected addend branch).card := by
      simp_rw [rnslBadOffsets, Finset.card_filter]

/-- Finite averaging selects one fixed offset with the strict three-per-step
straight-line bound. -/
theorem exists_fixed_offset_rnsl
    (offsets : Finset G) (branches : Finset Branch)
    (offsetsNonempty : offsets.Nonempty) (stepCount : Nat)
    (selected : Branch → Fin stepCount → Bool)
    (addend : Fin stepCount → G) :
    ∃ offset ∈ offsets,
      offsets.card *
          (rnslBadBranches branches stepCount selected addend offset).card ≤
        branches.card * (3 * stepCount) := by
  classical
  have totalBadBound :
      ∑ offset ∈ offsets,
          (rnslBadBranches branches stepCount selected addend offset).card ≤
        branches.card * (3 * stepCount) := by
    rw [sum_rnslBadBranches_eq_sum_rnslBadOffsets]
    calc
      ∑ branch ∈ branches,
          (rnslBadOffsets offsets stepCount selected addend branch).card ≤
          ∑ _branch ∈ branches, 3 * stepCount := by
        exact Finset.sum_le_sum fun branch _ =>
          rnslBadOffsets_card_le_three_mul offsets stepCount selected addend
            branch
      _ = branches.card * (3 * stepCount) := by simp
  have scaledTotal :
      ∑ offset ∈ offsets,
          offsets.card *
            (rnslBadBranches branches stepCount selected addend offset).card ≤
        ∑ _offset ∈ offsets, branches.card * (3 * stepCount) := by
    calc
      ∑ offset ∈ offsets,
          offsets.card *
            (rnslBadBranches branches stepCount selected addend offset).card =
          offsets.card *
            ∑ offset ∈ offsets,
              (rnslBadBranches branches stepCount selected addend offset).card := by
        rw [Finset.mul_sum]
      _ ≤ offsets.card * (branches.card * (3 * stepCount)) :=
        Nat.mul_le_mul_left offsets.card totalBadBound
      _ = ∑ _offset ∈ offsets, branches.card * (3 * stepCount) := by simp
  exact Finset.exists_le_of_sum_le offsetsNonempty scaledTotal

end

end ExceptionalOffsetAveraging
end QuantumAlg

end
