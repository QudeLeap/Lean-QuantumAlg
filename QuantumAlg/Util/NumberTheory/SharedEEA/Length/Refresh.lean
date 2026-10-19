/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.NumberTheory.SharedEEA.PackingBoundary
import all QuantumAlg.Util.NumberTheory.SharedEEA.PhysicalWindow

/-!
# Actual coefficient-length refresh from the exchanged work words

After the whole-word swap, the source reads the old coefficient from the
second word and the new coefficient from the first word. It XORs the old
length into the retained length register, then XORs the new length
[LYL+26, sec_circuit/sub_block_new.tex:211-219,338-341]. Both reads use the
actual left region ending before the old divisor boundary
[LYL+26, sec_EEA/sub_regshare.tex:309-312].

The finite-word operations below follow those two serial XOR writes.
Exact extraction and the proved boundary resegmentation recover the
coefficients from the actual completed work words. Reachable macro
capacity proves their lengths fit the stated finite length register,
including the final coefficient equal to the modulus. Reverse-order XOR
writes recover every prior length-register value without changing the
work words. Location-controlled gate synthesis and resource accounting
remain separate from these arithmetic and physical-window laws.
-/

namespace QuantumAlg.NumberTheory.SharedEEA.LengthRefresh

variable {wordWidth coefficientWidth remainderWidth clockWidth : Nat}

/-- Reading the actual left region of a packed pair recovers its entire arithmetic coefficient. -/
lemma read_left_work2 (payload : WordPacking.Work2Payload coefficientWidth remainderWidth)
    (widths : coefficientWidth + remainderWidth = wordWidth) :
    PhysicalWindow.read coefficientWidth ((WordPacking.packWork2 payload).cast widths) =
      payload.coefficientBits := by
  apply BitVec.eq_of_getLsbD_eq
  intro index within
  rw [PhysicalWindow.read_bit _ (by omega) index within, BitVec.getMsbD_cast,
    WordPacking.packWork2_coefficient_bit payload index within]

/-- Execute the source's old-length XOR followed by its new-length XOR. -/
def serialXor (length oldLength newLength : BitVec clockWidth) : BitVec clockWidth :=
  (length ^^^ oldLength) ^^^ newLength

/-- The two actual writes replace a correctly retained old length by the new length. -/
lemma serialXor_old (oldLength newLength : BitVec clockWidth) :
    serialXor oldLength oldLength newLength = newLength := by
  simp only [serialXor, BitVec.xor_self, BitVec.zero_xor]

/-- Reversing those same writes restores every input length-register value exactly. -/
lemma serialXor_reverse (length oldLength newLength : BitVec clockWidth) :
    serialXor (serialXor length oldLength newLength) newLength oldLength = length := by
  unfold serialXor
  rw [BitVec.xor_assoc (length ^^^ oldLength) newLength newLength,
    BitVec.xor_self, BitVec.xor_zero, BitVec.xor_assoc length oldLength oldLength,
    BitVec.xor_self, BitVec.xor_zero]

/-- Refresh from the two actual post-swap left windows, in the specified old-then-new order. -/
def coefficientUpdate (readWidth : Nat) (first second : BitVec wordWidth)
    (length : BitVec clockWidth) : BitVec clockWidth :=
  serialXor length
    (BitVec.ofNat clockWidth (PhysicalWindow.read readWidth second).toNat.size)
    (BitVec.ofNat clockWidth (PhysicalWindow.read readWidth first).toNat.size)

/-- Reading the same untouched work words in reverse order undoes the length update. -/
lemma coefficientUpdate_reverse (readWidth : Nat) (first second : BitVec wordWidth)
    (length : BitVec clockWidth) :
    coefficientUpdate readWidth second first (coefficientUpdate readWidth first second length) =
      length :=
  serialXor_reverse length _ _

private lemma old_coefficient_fits (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    state.coefficient < 2 ^ CoefficientCapacity.work2CoefficientWidth state modulus := by
  have nextBound := CoefficientCapacity.value_fits state modulus state.quotient.size
    valid conserved active
  change (CoefficientPhase.finish state.coefficient (CoefficientPhase.start state)).value <
    2 ^ CoefficientCapacity.work2CoefficientWidth state modulus at nextBound
  rw [CoefficientPhase.finish_start_coefficient] at nextBound
  exact (IterationState.coefficient_lt_step state valid active).trans nextBound

/-- View the completed old first word at the actual common read boundary after the swap. -/
private def oldReadPayload (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    WordPacking.Work2Payload (CoefficientCapacity.work2CoefficientWidth state modulus)
      state.divisor.size where
  coefficientBits := BitVec.ofNatLT state.coefficient
    (old_coefficient_fits state modulus valid conserved active)
  remainderBits := BitVec.ofNatLT (state.remainder % state.divisor)
    ((Nat.mod_lt _ active).trans (Nat.lt_size_self state.divisor))

/-- The old coefficient is read from the actual post-swap second word at the source boundary. -/
lemma read_old_coefficient (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus)
      (PackingBoundary.completedFirstWord state modulus valid conserved)).toNat =
        state.coefficient := by
  have resegmented : PackingBoundary.completedFirstWord state modulus valid conserved =
      (WordPacking.packWork2 (oldReadPayload state modulus valid conserved active)).cast
        (CoefficientCapacity.work2_width state modulus valid conserved) := by
    unfold PackingBoundary.completedFirstWord
    apply PackingBoundary.work1_resegment
    · change (CoefficientPhase.finish state.coefficient
        (CoefficientPhase.start state)).remaining = 0
      exact CoefficientPhase.finish_remaining _ _
    · rfl
    · rfl
  rw [resegmented, read_left_work2]
  rfl

/-- The new coefficient is read from the actual post-swap first word at that same boundary. -/
lemma read_new_coefficient (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (PhysicalWindow.read (CoefficientCapacity.work2CoefficientWidth state modulus)
      (PackingBoundary.completedSecondWord state modulus valid conserved active)).toNat =
        (IterationState.step state).coefficient := by
  unfold PackingBoundary.completedSecondWord
  rw [read_left_work2]
  exact CoefficientPhase.finish_start_coefficient state

/-- A value bounded by the modulus has its exact length in the stated finite length register. -/
lemma length_fits (value modulus : Nat) (bounded : value ≤ modulus) :
    value.size < 2 ^ modulus.size.size :=
  (Nat.size_le_size bounded).trans_lt (Nat.lt_size_self modulus.size)

/-- The source's finite length encoding retains the actual size without truncation. -/
lemma encoded_length_toNat (value modulus : Nat) (bounded : value ≤ modulus) :
    (BitVec.ofNat modulus.size.size value.size).toNat = value.size := by
  change value.size % 2 ^ modulus.size.size = value.size
  exact Nat.mod_eq_of_lt (length_fits value modulus bounded)

/-- The actual reads and XOR writes give the complete next finite coefficient-length register. -/
lemma coefficient_update_exact (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    coefficientUpdate (CoefficientCapacity.work2CoefficientWidth state modulus)
        (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size state.coefficient.size) =
      BitVec.ofNat modulus.size.size (IterationState.step state).coefficient.size := by
  unfold coefficientUpdate
  rw [read_old_coefficient state modulus valid conserved active,
    read_new_coefficient state modulus valid conserved active]
  exact serialXor_old _ _

/-- The actual refreshed register decodes to the new coefficient length, also at termination. -/
lemma coefficient_update_toNat (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    (coefficientUpdate (CoefficientCapacity.work2CoefficientWidth state modulus)
        (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (BitVec.ofNat modulus.size.size state.coefficient.size)).toNat =
      (IterationState.step state).coefficient.size := by
  rw [coefficient_update_exact state modulus valid conserved active]
  exact encoded_length_toNat _ modulus
    (Capacity.iteration_fields_le (IterationState.step state) modulus
      (IterationState.step_admissible state valid active)
      ((IterationState.step_balance state).trans conserved)).2.2.1

/-- Reversing the actual exchanged-word reads restores the precise old finite length register. -/
lemma coefficient_update_restores (state : IterationState) (modulus : Nat)
    (valid : state.Admissible) (conserved : state.balance = modulus)
    (active : 0 < state.divisor) :
    coefficientUpdate (CoefficientCapacity.work2CoefficientWidth state modulus)
        (PackingBoundary.completedFirstWord state modulus valid conserved)
        (PackingBoundary.completedSecondWord state modulus valid conserved active)
        (BitVec.ofNat modulus.size.size (IterationState.step state).coefficient.size) =
      BitVec.ofNat modulus.size.size state.coefficient.size := by
  rw [← coefficient_update_exact state modulus valid conserved active]
  exact coefficientUpdate_reverse _ _ _ _

end QuantumAlg.NumberTheory.SharedEEA.LengthRefresh
