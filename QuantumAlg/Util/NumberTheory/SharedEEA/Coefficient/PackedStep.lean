/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Coefficient.Window
import all QuantumAlg.Util.NumberTheory.SharedEEA.Division.PackedStep

/-!
# Exact Work1 resegmentation after consuming a coefficient-phase quotient bit

The source exchanges the lowest live quotient bit with zero Sign before
decrementing its retained length [LYL+26, sec_EEA/sub_regshare.tex:288-296].
The quotient region loses precisely that bit and the remainder region gains
one real leading zero. The whole original word therefore becomes the next
literal coefficient-phase payload, not merely a same-cardinality encoding.

The effective quotient lengths and all physical widths follow from the
actual coefficient run and conserved macro invariant. Equality and zero
remainder are retained; no range premise is imposed on the eventual input.
This owner proves finite packing mathematics for the existing native
exchange, whose complete gate action is connected separately.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.CoefficientPackedStep

open CoefficientCapacity

/-- Consuming one actual quotient bit enlarges the literal remainder region by exactly one bit. -/
theorem remainder_width_succ (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    work1RemainderWidth state modulus (count + 1) =
      work1RemainderWidth state modulus count + 1 := by
  have capacity := work1_capacity state modulus count valid conserved
  unfold work1RemainderWidth
  omega

/-- The coefficient, separator, and unconsumed higher quotient bits form the retained prefix. -/
def retainedPrefix (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    BitVec ((state.coefficient.size + 1) + (state.quotient.size - (count + 1))) :=
  let next := work1Payload state modulus (count + 1) valid conserved
  (next.coefficientBits.reverse ++ (0 : BitVec 1)) ++ next.quotientBits

private theorem half_prefix_nat (head quotient oldWidth nextWidth : Nat)
    (widthEq : oldWidth = nextWidth + 1) :
    (head * 2 ^ oldWidth + quotient) / 2 = head * 2 ^ nextWidth + quotient / 2 := by
  rw [widthEq, Nat.pow_succ]
  rw [show head * (2 ^ nextWidth * 2) + quotient =
    quotient + (head * 2 ^ nextWidth) * 2 by ring,
    Nat.add_mul_div_right _ _ (by decide : 0 < 2), Nat.add_comm]

private theorem resegment_nat (head quotient remainder quotientWidth oldWidth nextWidth : Nat)
    (widthEq : nextWidth = oldWidth + 1) :
    (head * 2 ^ quotientWidth + quotient) * 2 ^ (oldWidth + 1) + remainder =
      head * 2 ^ (quotientWidth + nextWidth) + (quotient * 2 ^ nextWidth + remainder) := by
  rw [widthEq]
  simp only [Nat.pow_add, Nat.pow_one]
  ring

private theorem fullPrefix_half (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    let old := work1Payload state modulus count valid conserved
    (((old.coefficientBits.reverse ++ (0 : BitVec 1)) ++ old.quotientBits).toNat / 2) =
      (retainedPrefix state modulus count valid conserved).toNat := by
  dsimp only
  let old := work1Payload state modulus count valid conserved
  let next := work1Payload state modulus (count + 1) valid conserved
  let head := old.coefficientBits.reverse ++ (0 : BitVec 1)
  have nextWidth : state.quotient.size - count = state.quotient.size - (count + 1) + 1 := by
    omega
  change (head ++ old.quotientBits).toNat / 2 = (head ++ next.quotientBits).toNat
  rw [DivisionPackedStep.append_toNat head old.quotientBits,
    DivisionPackedStep.append_toNat head next.quotientBits]
  change (head.toNat * 2 ^ (state.quotient.size - count) +
      (CoefficientWindow.current state count).remaining) / 2 =
    head.toNat * 2 ^ (state.quotient.size - (count + 1)) +
      (CoefficientWindow.current state count).remaining / 2
  exact half_prefix_nat head.toNat (CoefficientWindow.current state count).remaining
    (state.quotient.size - count) (state.quotient.size - (count + 1)) nextWidth

/-- Reading above the consumed bit returns exactly the actual next quotient prefix. -/
theorem original_prefix (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    ((WordPacking.packWork1 (work1Payload state modulus count valid conserved)).extractLsb'
      (work1RemainderWidth state modulus count + 1)
      ((state.coefficient.size + 1) + (state.quotient.size - (count + 1)))).toNat =
        (retainedPrefix state modulus count valid conserved).toNat := by
  let old := work1Payload state modulus count valid conserved
  let head := old.coefficientBits.reverse ++ (0 : BitVec 1)
  let kept := retainedPrefix state modulus count valid conserved
  have assemble : (head ++ old.quotientBits) ++ old.remainderBits =
      (head ++ (old.quotientBits ++ old.remainderBits)).cast (by omega) := BitVec.append_assoc
  have read := congrArg
    (fun word : BitVec (((state.coefficient.size + 1) + (state.quotient.size - count)) +
      work1RemainderWidth state modulus count) =>
      (word.extractLsb' (work1RemainderWidth state modulus count + 1)
        ((state.coefficient.size + 1) + (state.quotient.size - (count + 1)))).toNat) assemble
  rw [BitVec.extractLsb'_append_eq_of_le (by omega), BitVec.extractLsb'_cast,
    Nat.add_sub_cancel_left] at read
  refine read.symm.trans ?_
  change ((((head ++ old.quotientBits).toNat >>> 1) %
    2 ^ ((state.coefficient.size + 1) + (state.quotient.size - (count + 1))))) = kept.toNat
  rw [Nat.shiftRight_eq_div_pow, show 2 ^ 1 = 2 by decide,
    fullPrefix_half state modulus count valid conserved beforeEnd]
  exact Nat.mod_eq_of_lt kept.isLt

/-- The complete lower remainder is retained before and after the quotient boundary changes. -/
theorem original_low (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus) :
    (WordPacking.packWork1 (work1Payload state modulus count valid conserved)).setWidth
      (work1RemainderWidth state modulus count) =
        (work1Payload state modulus count valid conserved).remainderBits := by
  let old := work1Payload state modulus count valid conserved
  have right : (WordPacking.packWork1 old).setWidth
      ((state.quotient.size - count) + work1RemainderWidth state modulus count) =
    old.quotientBits ++ old.remainderBits := BitVec.setWidth_append_eq_right
  have lower := congrArg
    (fun word : BitVec ((state.quotient.size - count) + work1RemainderWidth state modulus count) =>
      word.setWidth (work1RemainderWidth state modulus count)) right
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_append_eq_right] at lower
  exact lower

/-- The physical bit immediately above that remainder is precisely the next actual quotient bit. -/
theorem original_digit (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    (WordPacking.packWork1 (work1Payload state modulus count valid conserved)).getLsbD
      (work1RemainderWidth state modulus count) =
        CoefficientPhase.lowBit (CoefficientWindow.current state count).remaining := by
  have inTail : work1RemainderWidth state modulus count <
      (state.quotient.size - count) + work1RemainderWidth state modulus count := by omega
  rw [WordPacking.packWork1, BitVec.getLsbD_append, if_pos inTail,
    BitVec.getLsbD_append, if_neg (Nat.lt_irrefl _), Nat.sub_self]
  change (CoefficientWindow.current state count).remaining.testBit 0 = _
  exact Nat.testBit_zero _

/-- The retained prefix and zero followed by the old remainder occupy the complete original word. -/
theorem assembly_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    ((state.coefficient.size + 1) + (state.quotient.size - (count + 1))) +
      (work1RemainderWidth state modulus count + 1) = modulus.size + 3 := by
  have complete := work1_width state modulus (count + 1) valid conserved
  rw [remainder_width_succ state modulus count valid conserved beforeEnd] at complete
  omega

/-- Literal whole word after the actual selected quotient position receives zero Sign. -/
def clearedWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) : BitVec (modulus.size + 3) :=
  (retainedPrefix state modulus count valid conserved ++ BitVec.cons false
    (work1Payload state modulus count valid conserved).remainderBits).cast
      (assembly_width state modulus count valid conserved beforeEnd)

/-- The actual cleared-bit layout is exactly the next full Work1 payload with its moved boundary. -/
theorem clearedWord_eq_next (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (beforeEnd : count < state.quotient.size) :
    clearedWord state modulus count valid conserved beforeEnd =
      (WordPacking.packWork1 (work1Payload state modulus (count + 1) valid conserved)).cast
        (work1_width state modulus (count + 1) valid conserved) := by
  let old := work1Payload state modulus count valid conserved
  let next := work1Payload state modulus (count + 1) valid conserved
  let head := old.coefficientBits.reverse ++ (0 : BitVec 1)
  apply BitVec.eq_of_toNat_eq
  change (((head ++ next.quotientBits) ++ BitVec.cons false old.remainderBits).cast
      (assembly_width state modulus count valid conserved beforeEnd)).toNat =
    ((head ++ (next.quotientBits ++ next.remainderBits)).cast
      (work1_width state modulus (count + 1) valid conserved)).toNat
  simp only [BitVec.toNat_cast, DivisionPackedStep.append_toNat, BitVec.toNat_cons',
    Bool.toNat_false, Nat.zero_shiftLeft, Nat.zero_add]
  change (head.toNat * 2 ^ (state.quotient.size - (count + 1)) +
      (CoefficientWindow.current state (count + 1)).remaining) *
        2 ^ (work1RemainderWidth state modulus count + 1) + state.remainder % state.divisor =
    head.toNat * 2 ^ ((state.quotient.size - (count + 1)) +
      work1RemainderWidth state modulus (count + 1)) +
        ((CoefficientWindow.current state (count + 1)).remaining *
          2 ^ work1RemainderWidth state modulus (count + 1) + state.remainder % state.divisor)
  exact resegment_nat head.toNat (CoefficientWindow.current state (count + 1)).remaining
    (state.remainder % state.divisor) (state.quotient.size - (count + 1))
    (work1RemainderWidth state modulus count) (work1RemainderWidth state modulus (count + 1))
    (remainder_width_succ state modulus count valid conserved beforeEnd)

end QuantumAlg.NumberTheory.SharedEEA.CoefficientPackedStep
