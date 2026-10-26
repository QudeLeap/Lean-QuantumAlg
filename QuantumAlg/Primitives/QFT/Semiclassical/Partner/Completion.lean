/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Prefix

/-!
# Partition of complete original outputs by their next chronological block

Every complete physical output extends exactly one current block outcome.
The finite-sum identity preserves arbitrary complete-output weights; it
asserts no uniformity or independence of Fourier outcomes.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open scoped BigOperators

/-- The next original coordinates, without changing their MSB-first order. -/
def segmentBits {full : Nat} (head tail : Nat) (within : tail + head ≤ full)
    (complete : Bits full) : Bits tail :=
  (binaryEquiv tail).symm (BinaryBasis.bigEndianEquiv tail
    (fun position => tupleCoordinates full complete
      (Fin.castLE within (suffixPosition head tail position))))

/-- The next block reads exactly the original complete output's selected coordinates. -/
lemma segmentBits_coordinate {full : Nat} (head tail : Nat) (within : tail + head ≤ full)
    (complete : Bits full) (position : Fin tail) :
    tupleCoordinates tail (segmentBits head tail within complete) position =
      tupleCoordinates full complete
        (Fin.castLE within (suffixPosition head tail position)) := by
  simp only [tupleCoordinates, segmentBits, Equiv.apply_symm_apply]
  exact congrFun ((BinaryBasis.bigEndianEquiv tail).symm_apply_apply _) position

/-- Its original next block appends to the unchanged previous prefix. -/
lemma prefixBits_append_segment {full : Nat} (head tail : Nat)
    (within : tail + head ≤ full) (complete : Bits full) :
    prefixBits (tail + head) within complete =
      blockBits head tail
        (prefixBits head ((Nat.le_add_left head tail).trans within) complete)
        (segmentBits head tail within complete) :=
  prefixBits_append head tail within complete (segmentBits head tail within complete)
    (segmentBits_coordinate head tail within complete)

private lemma blockBits_eq_iff (head tail : Nat)
    (firstFront lastFront : Bits head) (firstBack lastBack : Bits tail) :
    blockBits head tail firstFront firstBack = blockBits head tail lastFront lastBack ↔
      firstFront = lastFront ∧ firstBack = lastBack := by
  constructor
  · intro same
    constructor
    · apply tupleCoordinates_injective head
      funext position
      have observed := congrArg
        (fun value => tupleCoordinates (tail + head) value (prefixPosition head tail position))
        same
      simpa only [blockBits_prefix] using observed
    · apply tupleCoordinates_injective tail
      funext position
      have observed := congrArg
        (fun value => tupleCoordinates (tail + head) value (suffixPosition head tail position))
        same
      simpa only [blockBits_suffix] using observed
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Extension of the enlarged prefix is exactly extension of both original blocks. -/
lemma prefixBits_append_eq_iff {full : Nat} (head tail : Nat)
    (within : tail + head ≤ full) (complete : Bits full)
    (front : Bits head) (outcome : Bits tail) :
    prefixBits (tail + head) within complete = blockBits head tail front outcome ↔
      prefixBits head ((Nat.le_add_left head tail).trans within) complete = front ∧
        segmentBits head tail within complete = outcome := by
  rw [prefixBits_append_segment, blockBits_eq_iff]

/-- Summing the original completions over each possible next block counts each exactly once. -/
lemma sum_prefix_completions {full : Nat} (head tail : Nat)
    (within : tail + head ≤ full) (front : Bits head) (weight : Fin (2 ^ full) → ℝ) :
    (∑ outcome : Bits tail, ∑ complete : Fin (2 ^ full),
      if prefixBits (tail + head) within ((binaryEquiv full).symm complete) =
          blockBits head tail front outcome
        then weight complete else 0) =
      ∑ complete : Fin (2 ^ full),
        if prefixBits head ((Nat.le_add_left head tail).trans within)
            ((binaryEquiv full).symm complete) = front
          then weight complete else 0 := by
  classical
  simp_rw [prefixBits_append_eq_iff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro complete _
  by_cases matched :
      prefixBits head ((Nat.le_add_left head tail).trans within)
        ((binaryEquiv full).symm complete) = front
  · simp [matched]
  · simp [matched]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
