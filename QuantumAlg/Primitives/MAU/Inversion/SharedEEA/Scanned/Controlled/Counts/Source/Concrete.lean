/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source.Comparison
import all QuantumAlg.Primitives.MAU.Addition.HRS.Split
import all QuantumAlg.Primitives.MAU.Addition.HRS.Carry.Resources
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Comparison.Arithmetic
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.SourceProgram
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Parameters
import Mathlib.Tactic.NormNum

/-!
# Kernel numerical evaluation of the actual fixed P-256 source constants

The structural evaluator below is proved equal to the independently
source-bound HRS recurrence. It evaluates only numerical coordinates;
no emitted gate list, operator, or measurement record is replaced.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts

noncomputable section

open Addition.HRS EncodedBit

private lemma block_sum (value : Nat → Nat) (width blocks : Nat) :
    (∑ index ∈ Finset.range (width * blocks), value index) =
      ∑ block ∈ Finset.range blocks,
        ∑ index ∈ Finset.range width, value (width * block + index) := by
  induction blocks with
  | zero => simp
  | succ blocks inductionHypothesis =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, inductionHypothesis]

private lemma padded_sum (value : Nat → Nat) (count capacity : Nat) (within : count ≤ capacity) :
    (∑ index ∈ Finset.range capacity, if index < count then value index else 0) =
      ∑ index ∈ Finset.range count, value index := by
  rw [show capacity = count + (capacity - count) by omega, Finset.sum_range_add]
  have first : (∑ index ∈ Finset.range count, if index < count then value index else 0) =
      ∑ index ∈ Finset.range count, value index := by
    apply Finset.sum_congr rfl
    intro index member
    rw [if_pos (Finset.mem_range.mp member)]
  have tail : (∑ index ∈ Finset.range (capacity - count),
      if count + index < count then value (count + index) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [if_neg (by omega)]
  rw [first, tail, Nat.add_zero]

private lemma highConstantCount_sum (constant count : Nat) :
    highConstantCount constant count =
      ∑ index ∈ Finset.range count, (constant.testBit (index + 1)).toNat := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [highConstantCount, inductionHypothesis, Finset.sum_range_succ]

/-- Eight fixed blocks retain each actual selected bit while bounding kernel reduction depth. -/
def blockedHighCount (constant count : Nat) : Nat :=
  ∑ block ∈ Finset.range 8, ∑ index ∈ Finset.range 32,
    if 32 * block + index < count then (constant.testBit (32 * block + index + 1)).toNat else 0

private lemma blockedHighCount_eq (constant count : Nat) (within : count ≤ 256) :
    blockedHighCount constant count = highConstantCount constant count := by
  rw [blockedHighCount, ← block_sum
    (fun index => if index < count then (constant.testBit (index + 1)).toNat else 0) 32 8]
  exact (padded_sum (fun index => (constant.testBit (index + 1)).toNat)
    count 256 within).trans (highConstantCount_sum constant count).symm

/-- The same carry arithmetic with a proved block evaluation of its selected constant bits. -/
def blockedCarryCount (width constant : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) : Nat :=
  match width with
  | 0 => 0
  | 1 => (constant.testBit 0).toNat * (if .gate .cnot = focus then 1 else 0)
  | n + 2 =>
      (blockedHighCount constant (n + 1) + blockedHighCount constant n) *
        ((if .gate .cnot = focus then 1 else 0) +
          2 * (if .gate .singleQubit = focus then 1 else 0)) +
        (2 * n + (constant.testBit 0).toNat +
          (if n = 0 then 0 else 2 * (n - 1) + (constant.testBit 0).toNat)) *
          (if .gate .toffoli = focus then 1 else 0)

private lemma blockedCarryCount_eq (width constant : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) (within : width ≤ 257) :
    blockedCarryCount width constant focus = carryCount width constant focus := by
  cases width with
  | zero => rfl
  | succ previous =>
      cases previous with
      | zero => rfl
      | succ tail =>
          simp only [blockedCarryCount, carryCount,
            blockedHighCount_eq constant (tail + 1) (by omega),
            blockedHighCount_eq constant tail (by omega)]

/-- A structurally recursive numerical evaluation with an explicit sufficient fuel bound. -/
def boundedOneDirtyCount : Nat → Nat → Nat →
    Resource.Event (.quantum AlgorithmGate.model .empty) → Nat
  | 0, _, _, _ => 0
  | fuel + 1, width, constant, focus =>
      if width ≤ 1 then
        ((List.ofFn fun bit : Fin width => bit).filter
          (fun bit => constant.testBit bit.val)).length *
            (if .gate .singleQubit = focus then 1 else 0)
      else
        2 * (incrementCount (highWidth width) focus +
          highWidth width * (if .gate .cnot = focus then 1 else 0) +
            blockedCarryCount (lowWidth width) (constant % 2 ^ lowWidth width) focus) +
          boundedOneDirtyCount fuel (lowWidth width) (constant % 2 ^ lowWidth width) focus +
          boundedOneDirtyCount fuel (highWidth width) (constant / 2 ^ lowWidth width) focus

/-- Sufficient fuel preserves the exact original HRS numerical count for every fixed constant. -/
lemma oneDirtyCount_bounded (fuel width : Nat) (constant : Fin (2 ^ width))
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) (enough : width ≤ fuel)
    (within : width ≤ 260) :
    oneDirtyCount width constant focus = boundedOneDirtyCount fuel width constant.val focus := by
  induction fuel generalizing width with
  | zero =>
      have zero : width = 0 := by omega
      subst width
      rw [oneDirtyCount, dif_pos (by omega)]
      simp only [Word.constantOneIndices, List.ofFn_zero, List.filter_nil, List.length_nil,
        Nat.zero_mul, boundedOneDirtyCount]
  | succ fuel inductionHypothesis =>
      rw [oneDirtyCount, boundedOneDirtyCount]
      by_cases base : width ≤ 1
      · rw [dif_pos base, if_pos base]
        rfl
      · have decrease := hrsSplit_decreases width (by omega)
        rw [dif_neg base, if_neg base,
          inductionHypothesis (lowWidth width) ((splitWord width) constant).1
            (by omega) (by omega),
          inductionHypothesis (highWidth width) ((splitWord width) constant).2
            (by omega) (by omega),
          hrsSplit_low_value, hrsSplit_high_value,
          blockedCarryCount_eq _ _ _ (by unfold lowWidth; omega)]

private abbrev p256 := EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus

/-- Exact public P-256 size, normalized before transporting any dependent native program. -/
lemma p256_size : p256.size = 256 := by
  have upper : p256.size ≤ 256 := Nat.size_le.mpr
    EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus_lt_capacity
  have lower : 255 < p256.size := Nat.lt_size.mpr (by
    norm_num [p256, EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus,
      EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.capacity,
      EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.complement,
      EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.width])
  omega

/-- All three literal coordinates of the complete fixed extended comparison offset. -/
lemma p256_extended_offset_numeric :
    boundedOneDirtyCount 260 260
        868440669293351439007219156594799476061116805617479355217893856408871488192512
        (.gate .toffoli) = 45470 ∧
      boundedOneDirtyCount 260 260
        868440669293351439007219156594799476061116805617479355217893856408871488192512
        (.gate .cnot) = 7654 ∧
      boundedOneDirtyCount 260 260
        868440669293351439007219156594799476061116805617479355217893856408871488192512
        (.gate .singleQubit) = 2799 := by
  decide

/-- All three literal coordinates of the complete fixed restoring comparison offset. -/
lemma p256_low_offset_numeric :
    boundedOneDirtyCount 259 259
        57896044605178124381348723474703786765043071707645157097766815654433548926976
        (.gate .toffoli) = 45178 ∧
      boundedOneDirtyCount 259 259
        57896044605178124381348723474703786765043071707645157097766815654433548926976
        (.gate .cnot) = 6402 ∧
      boundedOneDirtyCount 259 259
        57896044605178124381348723474703786765043071707645157097766815654433548926976
        (.gate .singleQubit) = 422 := by
  decide

/-- All three literal coordinates of the complete fixed reflection offset. -/
lemma p256_reflection_offset_numeric :
    boundedOneDirtyCount 259 259
        810544624688173314625870433120095689296073733909834198120127040754437939265536
        (.gate .toffoli) = 45324 ∧
      boundedOneDirtyCount 259 259
        810544624688173314625870433120095689296073733909834198120127040754437939265536
        (.gate .cnot) = 7612 ∧
      boundedOneDirtyCount 259 259
        810544624688173314625870433120095689296073733909834198120127040754437939265536
        (.gate .singleQubit) = 2746 := by
  decide


private lemma split_power (base whole left right : Nat) (same : whole = left + right) :
    base ^ whole = base ^ left * base ^ right := by rw [same, pow_add]

/-- Public work capacity, evaluated through two smaller powers within the default exponent cap. -/
lemma p256_work_capacity : 2 ^ 259 =
    926336713898529563388567880069503262826159877325124512315660672063305037119488 := by
  calc
    2 ^ 259 = 2 ^ 256 * 2 ^ 3 := split_power 2 259 256 3 rfl
    _ = _ := by norm_num

private lemma extendedPivot_value (width pivot : Nat) :
    (Addition.Gidney.extendedNegatedPivot width pivot).val =
      (2 ^ width - pivot) % 2 ^ width := by rfl

private lemma lowPivot_value (width pivot : Nat) :
    (Addition.Gidney.pivotWord width pivot).val = pivot % 2 ^ width := rfl

private lemma negativePivot_value (width pivot : Nat) :
    (Addition.Gidney.negatedPivot width pivot).val = (2 ^ width - pivot) % 2 ^ width := rfl

/-- Fixed comparison coordinates retain both complete offsets and the actual final flag X. -/
lemma p256_comparison_numeric :
    comparisonCount (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.comparisonPivot p256) (.gate .toffoli) = 90648 ∧
      comparisonCount (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.comparisonPivot p256) (.gate .cnot) = 14056 ∧
      comparisonCount (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.comparisonPivot p256) (.gate .singleQubit) = 3222 := by
  have width : FoldSourceProgram.wordWidth p256 = 259 := by
    have size : p256.size = 256 := p256_size
    unfold FoldSourceProgram.wordWidth
    rw [size]
  have pivot : (FoldSourceProgram.comparisonPivot p256).val =
      57896044605178124381348723474703786765043071707645157097766815654433548926976 := by
    change p256 / 2 + 1 = _
    unfold p256
    rw [EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus_eq_standard]
    norm_num
  have nonzero : (FoldSourceProgram.comparisonPivot p256).val ≠ 0 := by rw [pivot]; decide
  have extendedValue :
      (Addition.Gidney.extendedNegatedPivot (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.comparisonPivot p256).val).val =
      868440669293351439007219156594799476061116805617479355217893856408871488192512 := by
    rw [extendedPivot_value]
    rw [pivot, width, p256_work_capacity]
  have lowValue :
      (Addition.Gidney.pivotWord (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.comparisonPivot p256).val).val =
      57896044605178124381348723474703786765043071707645157097766815654433548926976 := by
    rw [lowPivot_value, pivot, width]
    exact Nat.mod_eq_of_lt (by rw [p256_work_capacity]; decide)
  have extendedCount (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
      oneDirtyCount (1 + FoldSourceProgram.wordWidth p256)
          (Addition.Gidney.extendedNegatedPivot (FoldSourceProgram.wordWidth p256)
            (FoldSourceProgram.comparisonPivot p256).val) focus =
        boundedOneDirtyCount 260 260
          868440669293351439007219156594799476061116805617479355217893856408871488192512
          focus := by
    rw [oneDirtyCount_bounded _ _ _ _ (Nat.le_refl _) (by omega),
      extendedValue, width]
  have lowCount (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
      oneDirtyCount (FoldSourceProgram.wordWidth p256)
          (Addition.Gidney.pivotWord (FoldSourceProgram.wordWidth p256)
            (FoldSourceProgram.comparisonPivot p256).val) focus =
        boundedOneDirtyCount 259 259
          57896044605178124381348723474703786765043071707645157097766815654433548926976
          focus := by
    rw [oneDirtyCount_bounded _ _ _ _ (Nat.le_refl _) (by omega),
      lowValue, width]
  simp only [comparisonCount, if_neg nonzero, extendedCount, lowCount,
    p256_extended_offset_numeric.1, p256_extended_offset_numeric.2.1,
    p256_extended_offset_numeric.2.2, p256_low_offset_numeric.1,
    p256_low_offset_numeric.2.1, p256_low_offset_numeric.2.2]
  decide

/-- The internally controlled reflection keeps every original HRS leaf and complement bit. -/
lemma p256_reflection_numeric :
    oneDirtyCount (FoldSourceProgram.wordWidth p256)
        (Addition.Gidney.negatedPivot (FoldSourceProgram.wordWidth p256)
          (FoldSourceProgram.reflectionPivot p256).val) (.gate .cnot) +
      4 * oneDirtyCount (FoldSourceProgram.wordWidth p256)
        (Addition.Gidney.negatedPivot (FoldSourceProgram.wordWidth p256)
          (FoldSourceProgram.reflectionPivot p256).val) (.gate .toffoli) = 188908 ∧
    oneDirtyCount (FoldSourceProgram.wordWidth p256)
        (Addition.Gidney.negatedPivot (FoldSourceProgram.wordWidth p256)
          (FoldSourceProgram.reflectionPivot p256).val) (.gate .singleQubit) +
      FoldSourceProgram.wordWidth p256 = 3005 := by
  have width : FoldSourceProgram.wordWidth p256 = 259 := by
    have size : p256.size = 256 := p256_size
    unfold FoldSourceProgram.wordWidth
    rw [size]
  have value :
      (Addition.Gidney.negatedPivot (FoldSourceProgram.wordWidth p256)
        (FoldSourceProgram.reflectionPivot p256).val).val =
      810544624688173314625870433120095689296073733909834198120127040754437939265536 := by
    rw [negativePivot_value]
    simp only [FoldSourceProgram.reflectionPivot]
    rw [width]
    unfold p256
    rw [EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.modulus_eq_standard,
      p256_work_capacity]
    norm_num
  have count (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
      oneDirtyCount (FoldSourceProgram.wordWidth p256)
          (Addition.Gidney.negatedPivot (FoldSourceProgram.wordWidth p256)
            (FoldSourceProgram.reflectionPivot p256).val) focus =
        boundedOneDirtyCount 259 259
          810544624688173314625870433120095689296073733909834198120127040754437939265536
          focus := by
    rw [oneDirtyCount_bounded _ _ _ _ (Nat.le_refl _) (by omega), value, width]
  rw [count, count, count, p256_reflection_offset_numeric.1,
    p256_reflection_offset_numeric.2.1, p256_reflection_offset_numeric.2.2, width]
  decide

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledCounts
