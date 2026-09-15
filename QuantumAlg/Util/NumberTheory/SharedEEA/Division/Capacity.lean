/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.Progress

/-!
# Packed capacity of actual intermediate division states

The source's second phase stores the fixed coefficient, effective quotient
prefix, and current remainder in the first word, while the second word
contains the unchanged previous coefficient and divisor at its remaining
circular shift [LYL+26, sec_EEA/sub_regshare.tex:16-20,279-287].

These bounds use the actual `DivisionProgress.current` reached from the
comparison-driven alignment loop. The current remainder is below the
current scaled divisor, so the prefix times that remainder is bounded by
the already subtracted contribution. Combining this with the conserved
macro cross-sum yields the intermediate triple capacity. Zero prefixes
and zero remainders use the individual and pair bounds, without imposing
positivity conditions on them.

The written quotient length is proved equal to its effective bit length.
All three actual natural-number fields are encoded with `BitVec.ofNatLT`,
including the zero-width initial quotient. The first word contains its
explicit coefficient separator, and both source words have exactly
`modulus.size + 3` bits. Circular right shifts implement the actual remaining
shift count; sign operations and complete phase-flag recovery remain
separate refinements of these arithmetic and encoding laws.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionCapacity

/-- The actual first-word triple and its separator fit at every genuine division position. -/
theorem work1_capacity (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    state.coefficient.size + 1 + (DivisionProgress.current state count).written +
        (DivisionProgress.current state count).remainder.size ≤ modulus.size + 3 := by
  let current := DivisionProgress.current state count
  obtain ⟨scale, decomposition, below, _⟩ :=
    DivisionProgress.current_invariants state count active within
  change current.remainder + current.quotientPrefix * current.scale * state.divisor =
    state.remainder at decomposition
  change current.remainder < current.scale * state.divisor at below
  have scalePositive : 0 < current.scale := by
    rw [scale]
    exact Nat.two_pow_pos _
  have weightedBound : current.quotientPrefix * (current.scale * state.divisor) ≤
      state.remainder := by
    rw [← Nat.mul_assoc]
    omega
  have prefixBound : current.quotientPrefix ≤ state.remainder :=
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos scalePositive active)).trans weightedBound
  have remainderBound : current.remainder ≤ state.remainder := by omega
  have fields := Capacity.iteration_fields_le state modulus valid conserved
  have macroProduct : state.coefficient * state.remainder ≤ modulus := by
    simpa only [conserved, Nat.mul_comm] using (IterationState.products_le_balance state).1
  have prefixProduct : state.coefficient * current.quotientPrefix ≤ modulus :=
    (Nat.mul_le_mul_left _ prefixBound).trans macroProduct
  have remainderProduct : state.coefficient * current.remainder ≤ modulus :=
    (Nat.mul_le_mul_left _ remainderBound).trans macroProduct
  have tripleProduct : state.coefficient * current.quotientPrefix * current.remainder ≤
      modulus := by
    calc
      _ = state.coefficient * (current.quotientPrefix * current.remainder) := by ring
      _ ≤ state.coefficient * (current.quotientPrefix * (current.scale * state.divisor)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ below.le)
      _ ≤ state.coefficient * state.remainder := Nat.mul_le_mul_left _ weightedBound
      _ ≤ modulus := macroProduct
  have capacity : state.coefficient.size + current.quotientPrefix.size +
      current.remainder.size ≤ modulus.size + 2 := by
    by_cases prefixZero : current.quotientPrefix = 0
    · have pair := Capacity.pair_size state.coefficient current.remainder modulus
        fields.2.2.1 (remainderBound.trans fields.1) remainderProduct
      have emptySize : current.quotientPrefix.size = 0 := by simp [prefixZero]
      omega
    · by_cases remainderZero : current.remainder = 0
      · have pair := Capacity.pair_size state.coefficient current.quotientPrefix modulus
          fields.2.2.1 (prefixBound.trans fields.1) prefixProduct
        have emptySize : current.remainder.size = 0 := by simp [remainderZero]
        omega
      · exact Capacity.positive_triple_size _ _ _ _ valid.coefficient_pos
          (Nat.pos_of_ne_zero prefixZero) (Nat.pos_of_ne_zero remainderZero) tripleProduct
  have prefixSize := DivisionProgress.current_prefix_size state count active within
  change current.quotientPrefix.size = current.written at prefixSize
  change state.coefficient.size + 1 + current.written + current.remainder.size ≤ modulus.size + 3
  omega

/-- The first-word remainder region follows the actual coefficient and written quotient regions. -/
def remainderWidth (state : IterationState) (modulus count : Nat) : Nat :=
  modulus.size + 3 -
    (state.coefficient.size + 1 + (DivisionProgress.current state count).written)

/-- These actual source regions occupy the complete first shared word. -/
theorem work1_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (state.coefficient.size + 1) +
        ((DivisionProgress.current state count).written + remainderWidth state modulus count) =
      modulus.size + 3 := by
  have capacity := work1_capacity state modulus count valid conserved active within
  unfold remainderWidth
  omega

/-- The actual subtraction result fits the region remaining after the live source boundaries. -/
theorem remainder_fits (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    (DivisionProgress.current state count).remainder <
      2 ^ remainderWidth state modulus count := by
  apply Nat.size_le.mp
  have capacity := work1_capacity state modulus count valid conserved active within
  unfold remainderWidth
  omega

/-- Encode all actual division coordinates at the prescribed source widths without truncation. -/
def work1Payload (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    WordPacking.Work1Payload state.coefficient.size (DivisionProgress.current state count).written
      (remainderWidth state modulus count) where
  coefficientBits := BitVec.ofNatLT state.coefficient (Nat.lt_size_self _)
  quotientBits := BitVec.ofNatLT (DivisionProgress.current state count).quotientPrefix
    (Nat.size_le.mp (Nat.le_of_eq
      (DivisionProgress.current_prefix_size state count active within)))
  remainderBits := BitVec.ofNatLT (DivisionProgress.current state count).remainder
    (remainder_fits state modulus count valid conserved active within)

/-- Literal packing and decoding recover the actual three natural-number coordinates exactly. -/
theorem work1_decode (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    let payload := work1Payload state modulus count valid conserved active within
    let recovered := WordPacking.unpackWork1 (WordPacking.packWork1 payload)
    recovered.coefficientBits.toNat = state.coefficient ∧
      recovered.quotientBits.toNat = (DivisionProgress.current state count).quotientPrefix ∧
      recovered.remainderBits.toNat = (DivisionProgress.current state count).remainder := by
  simp only [WordPacking.unpackWork1_packWork1, work1Payload, BitVec.toNat_ofNatLT,
    and_self]

/-- The initial source quotient field has exactly zero physical bits. -/
theorem initial_quotient_width (state : IterationState) :
    (DivisionProgress.current state 0).written = 0 :=
  DivisionProgress.current_written state 0

/-- The unchanged previous coefficient fits beside its divisor throughout phase two. -/
theorem previous_coefficient_fits (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    state.previousCoefficient < 2 ^ CoefficientCapacity.work2CoefficientWidth state modulus := by
  apply Nat.size_le.mp
  have capacity := (Capacity.iteration_pair_sizes state modulus valid conserved).2
  unfold CoefficientCapacity.work2CoefficientWidth
  omega

/-- Encode the second word's actual unchanged coordinates before its remaining circular shift. -/
def work2Payload (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    WordPacking.Work2Payload (CoefficientCapacity.work2CoefficientWidth state modulus)
      state.divisor.size where
  coefficientBits := BitVec.ofNatLT state.previousCoefficient
    (previous_coefficient_fits state modulus valid conserved)
  remainderBits := BitVec.ofNatLT state.divisor (Nat.lt_size_self _)

/-- The second word also occupies exactly the source's fixed shared-word width. -/
theorem work2_width (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    CoefficientCapacity.work2CoefficientWidth state modulus + state.divisor.size =
      modulus.size + 3 :=
  CoefficientCapacity.work2_width state modulus valid conserved

/-- Decoding at the actual remaining shift recovers the previous coefficient and divisor. -/
theorem rotated_work2_decode (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    let shift := (Alignment.align state.remainder state.divisor).places - count
    let payload := work2Payload state modulus valid conserved
    let recovered := WordRotation.unpackRotatedWork2 shift
      (WordRotation.packRotatedWork2 shift payload)
    recovered.coefficientBits.toNat = state.previousCoefficient ∧
      recovered.remainderBits.toNat = state.divisor := by
  simp only [WordRotation.unpackRotatedWork2_packRotatedWork2, work2Payload,
    BitVec.toNat_ofNatLT, and_self]

/-- The literal source right rotation advances the actual remaining-shift encoding by one step. -/
theorem rotated_work2_step (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (WordRotation.packRotatedWork2
        ((Alignment.align state.remainder state.divisor).places - count)
        (work2Payload state modulus valid conserved)).rotateRight 1 =
      WordRotation.packRotatedWork2
        ((Alignment.align state.remainder state.divisor).places - (count + 1))
        (work2Payload state modulus valid conserved) := by
  have displacement : (Alignment.align state.remainder state.divisor).places - count =
      ((Alignment.align state.remainder state.divisor).places - (count + 1)) + 1 := by omega
  rw [displacement]
  exact WordRotation.packRotatedWork2_unshift _ _

/-- Every original input has enough space at every actual second-phase position after folding. -/
theorem folded_capacity (modulus input : Nat)
    (positive : 0 < input) (bounded : input < modulus) :
    let state := IterationState.initial modulus (foldInput modulus input).2
    ∀ count, count ≤ (Alignment.align state.remainder state.divisor).places →
      state.coefficient.size + 1 + (DivisionProgress.current state count).written +
          (DivisionProgress.current state count).remainder.size ≤ modulus.size + 3 := by
  dsimp only
  intro count within
  exact work1_capacity _ _ _ (folded_initial_admissible modulus input positive bounded)
    (IterationState.initial_balance modulus _) (foldInput_positive_half _ _ positive bounded).1
    within

end QuantumAlg.NumberTheory.SharedEEA.DivisionCapacity
