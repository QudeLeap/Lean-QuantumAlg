/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.RemainderLength

/-!
# Sequential refresh and recovery of both physical length registers

The source first refreshes the coefficient length using the old divisor
length, then refreshes the divisor length using the newly written
coefficient length [LYL+26, sec_EEA/sub_regshare.tex:311-313]. Both
refreshes use the two serial XOR writes on values read from the actual
exchanged work words [LYL+26, sec_circuit/sub_block_new.tex:211-219].

This is a composition of those concrete finite-word operations. Its
inverse restores the divisor length first, then uses that restored
boundary to undo the coefficient-length writes. Both inverse laws hold
for arbitrary finite register contents. At a reachable macro exchange,
the exact results are the two next field lengths, with no truncation.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.LengthPair

variable {wordWidth clockWidth : Nat}

/-- Refresh the two actual length registers in the source's order and dependent read windows. -/
def update (first second : BitVec wordWidth) (lengths : BitVec clockWidth × BitVec clockWidth) :
    BitVec clockWidth × BitVec clockWidth :=
  let coefficient := LengthRefresh.coefficientUpdate (wordWidth - lengths.2.toNat)
    first second lengths.1
  let divisor := RemainderLength.remainderUpdate (wordWidth - 1 - coefficient.toNat)
    first second lengths.2
  (coefficient, divisor)

/-- Undo the divisor writes first, then recover the old coefficient-read boundary and register. -/
def rewind (first second : BitVec wordWidth) (lengths : BitVec clockWidth × BitVec clockWidth) :
    BitVec clockWidth × BitVec clockWidth :=
  let divisor := RemainderLength.remainderUpdate (wordWidth - 1 - lengths.1.toNat)
    second first lengths.2
  let coefficient := LengthRefresh.coefficientUpdate (wordWidth - divisor.toNat)
    second first lengths.1
  (coefficient, divisor)

/-- Reverse-order actual writes restore both arbitrary finite length registers. -/
lemma rewind_update (first second : BitVec wordWidth)
    (lengths : BitVec clockWidth × BitVec clockWidth) :
    rewind first second (update first second lengths) = lengths := by
  simp only [rewind, update, RemainderLength.remainderUpdate_reverse,
    LengthRefresh.coefficientUpdate_reverse]

/-- The concrete inverse recovers every candidate output pair in the other direction. -/
lemma update_rewind (first second : BitVec wordWidth)
    (lengths : BitVec clockWidth × BitVec clockWidth) :
    update first second (rewind first second lengths) = lengths := by
  simp only [update, rewind, LengthRefresh.coefficientUpdate_reverse,
    RemainderLength.remainderUpdate_reverse]

/-- Reachable macro exchange supplies the exact two next finite lengths under the actual update. -/
lemma iteration_update (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    update (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size state.coefficient.size,
          BitVec.ofNat modulus.size.size state.divisor.size) =
      (BitVec.ofNat modulus.size.size (IterationState.step state).coefficient.size,
        BitVec.ofNat modulus.size.size (IterationState.step state).divisor.size) := by
  have oldDivisor := LengthRefresh.encoded_length_toNat state.divisor modulus
    (Capacity.iteration_fields_le state modulus valid conserved).2.1
  have coefficientExact : LengthRefresh.coefficientUpdate
      (modulus.size + 3 - state.divisor.size)
      (PackingBoundary.completedSecondWord state modulus valid conserved active)
      (PackingBoundary.completedFirstWord state modulus valid conserved)
      (BitVec.ofNat modulus.size.size state.coefficient.size) =
        BitVec.ofNat modulus.size.size (IterationState.step state).coefficient.size :=
    LengthRefresh.coefficient_update_exact state modulus valid conserved active
  have newCoefficient := LengthRefresh.encoded_length_toNat
    (IterationState.step state).coefficient modulus
    (Capacity.iteration_fields_le (IterationState.step state) modulus
      (IterationState.step_admissible state valid active)
      ((IterationState.step_balance state).trans conserved)).2.2.1
  have region : modulus.size + 3 - 1 - (IterationState.step state).coefficient.size =
      PackingBoundary.firstRemainderWidth (IterationState.step state) modulus := by
    unfold PackingBoundary.firstRemainderWidth
    omega
  simp only [update, oldDivisor, coefficientExact, newCoefficient, region,
    RemainderLength.remainder_update_exact
      state modulus valid conserved active]

/-- The same physical words recover both exact previous finite lengths from the updated pair. -/
lemma iteration_rewind (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    rewind (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size (IterationState.step state).coefficient.size,
          BitVec.ofNat modulus.size.size (IterationState.step state).divisor.size) =
      (BitVec.ofNat modulus.size.size state.coefficient.size,
        BitVec.ofNat modulus.size.size state.divisor.size) := by
  rw [← iteration_update state modulus valid conserved active]
  exact rewind_update _ _ _

end QuantumAlg.NumberTheory.SharedEEA.LengthPair
