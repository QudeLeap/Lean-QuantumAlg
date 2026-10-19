/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.Signed.Division.Phase

/-!
# Exact full-word quotient/remainder boundary after one division instruction

The source writes one quotient bit at the old remainder's highest physical
position, retaining the earlier quotient prefix and coefficient separator
[LYL+26, sec_EEA/sub_regshare.tex:16-17,279-287]. Consequently the same bits
admit two consecutive segmentations: the old prefix followed by the complete
signed-instruction output, or the next quotient prefix followed by the next
shorter remainder.

The equality below concerns the complete finite shared word. All widths
come from actual reachable division positions, and the instruction's next
quotient and remainder laws establish the resegmentation. It is not a
dimension-only cast or an additional execution rule. Actual native prefix
preservation is supplied by the physical selector owner.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.DivisionPackedStep

private lemma append_toNat {leftWidth rightWidth : Nat}
    (left : BitVec leftWidth) (right : BitVec rightWidth) :
    (left ++ right).toNat = left.toNat * 2 ^ rightWidth + right.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt right.isLt, Nat.shiftLeft_eq]

private lemma bool_toNat (value : Bool) : value.toNat = if value then 1 else 0 := by
  cases value <;> rfl

/-- The retained physical coefficient, explicit separator, and already written quotient prefix. -/
def retainedPrefix (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (within : count ≤ (Alignment.align state.remainder state.divisor).places) :
    BitVec ((state.coefficient.size + 1) + (DivisionProgress.current state count).written) :=
  let payload := DivisionCapacity.work1Payload state modulus count valid conserved active within
  (payload.coefficientBits.reverse ++ (0 : BitVec 1)) ++ payload.quotientBits

/-- The old prefix and full instruction output occupy exactly the original complete shared word. -/
lemma assembly_width (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    ((state.coefficient.size + 1) + (DivisionProgress.current state count).written) +
        (SignedDivisionPhase.nextWidth state modulus count + 1) = modulus.size + 3 := by
  have complete := DivisionCapacity.work1_width state modulus count
    valid conserved active beforeEnd.le
  rw [DivisionThreshold.remainder_width_succ state modulus count
    valid conserved active beforeEnd] at complete
  change ((state.coefficient.size + 1) + (DivisionProgress.current state count).written) +
    (DivisionCapacity.remainderWidth state modulus (count + 1) + 1) = modulus.size + 3
  omega

/-- Literal complete old prefix followed by the actual finite signed-instruction output word. -/
def instructionWord (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    BitVec (modulus.size + 3) :=
  (retainedPrefix state modulus count valid conserved active beforeEnd.le ++
    (SignedDivisionPhase.instruction state modulus count valid conserved active beforeEnd).2).cast
      (assembly_width state modulus count valid conserved active beforeEnd)

private lemma instruction_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (SignedDivisionPhase.instruction state modulus count valid conserved active beforeEnd).2.toNat =
      (SignedDivisionPhase.instruction state modulus count
        valid conserved active beforeEnd).2.msb.toNat *
        2 ^ SignedDivisionPhase.nextWidth state modulus count +
          (DivisionProgress.current state (count + 1)).remainder := by
  let result := (SignedDivisionPhase.instruction state modulus count
    valid conserved active beforeEnd).2
  have low := (SignedDivisionPhase.instruction_spec state modulus count
    valid conserved active beforeEnd).2.2
  calc
    _ = (BitVec.cons result.msb
        (result.setWidth (SignedDivisionPhase.nextWidth state modulus count))).toNat :=
      (congrArg BitVec.toNat (BitVec.cons_msb_setWidth result)).symm
    _ = _ := by
      rw [BitVec.toNat_cons', Nat.shiftLeft_eq]
      exact congrArg (fun value => result.msb.toNat *
        2 ^ SignedDivisionPhase.nextWidth state modulus count + value) low

/-- Appending the actual instruction digit is the next full finite quotient-prefix value. -/
lemma quotient_toNat (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    (DivisionProgress.current state (count + 1)).quotientPrefix =
      2 * (DivisionProgress.current state count).quotientPrefix +
        (SignedDivisionPhase.instruction state modulus count
          valid conserved active beforeEnd).2.msb.toNat := by
  rw [bool_toNat]
  exact SignedDivisionPhase.instruction_quotient state modulus count
    valid conserved active beforeEnd

/-- The complete word is exactly the next source packing with its moved field boundary. -/
lemma instructionWord_eq_next (state : IterationState) (modulus count : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor)
    (beforeEnd : count < (Alignment.align state.remainder state.divisor).places) :
    instructionWord state modulus count valid conserved active beforeEnd =
      (WordPacking.packWork1 (DivisionCapacity.work1Payload state modulus (count + 1)
        valid conserved active (by omega))).cast
          (DivisionCapacity.work1_width state modulus (count + 1)
            valid conserved active (by omega)) := by
  let old := DivisionCapacity.work1Payload state modulus count
    valid conserved active beforeEnd.le
  let next := DivisionCapacity.work1Payload state modulus (count + 1)
    valid conserved active (by omega)
  let head := old.coefficientBits.reverse ++ (0 : BitVec 1)
  let result := (SignedDivisionPhase.instruction state modulus count
    valid conserved active beforeEnd).2
  apply BitVec.eq_of_toNat_eq
  change (((head ++ old.quotientBits) ++ result).cast
    (assembly_width state modulus count valid conserved active beforeEnd)).toNat =
      ((head ++ (next.quotientBits ++ next.remainderBits)).cast
        (DivisionCapacity.work1_width state modulus (count + 1)
          valid conserved active (by omega))).toNat
  simp only [BitVec.toNat_cast, append_toNat]
  change (head.toNat * 2 ^ (DivisionProgress.current state count).written +
      (DivisionProgress.current state count).quotientPrefix) *
        2 ^ (SignedDivisionPhase.nextWidth state modulus count + 1) + result.toNat =
    head.toNat * 2 ^ ((DivisionProgress.current state (count + 1)).written +
      SignedDivisionPhase.nextWidth state modulus count) +
        ((DivisionProgress.current state (count + 1)).quotientPrefix *
          2 ^ SignedDivisionPhase.nextWidth state modulus count +
            (DivisionProgress.current state (count + 1)).remainder)
  have instructionNat := instruction_toNat state modulus count valid conserved active beforeEnd
  change result.toNat = result.msb.toNat *
    2 ^ SignedDivisionPhase.nextWidth state modulus count +
      (DivisionProgress.current state (count + 1)).remainder at instructionNat
  have quotient := quotient_toNat state modulus count valid conserved active beforeEnd
  change (DivisionProgress.current state (count + 1)).quotientPrefix =
    2 * (DivisionProgress.current state count).quotientPrefix + result.msb.toNat at quotient
  rw [instructionNat, quotient]
  simp only [DivisionProgress.current_written, Nat.pow_add, Nat.pow_one]
  ring

end QuantumAlg.NumberTheory.SharedEEA.DivisionPackedStep
