/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Subtraction

/-!
# Exact finite signed words of the existing TTK output specifications

The explicit arbitrary TTK overflow output is the high bit of the target
word. Its carry xor therefore agrees with addition of the source to that
complete finite word [TTK09, qic-loglogaddition-quant.tex:285-318]. Reversing
the already implemented addition gives the corresponding complete-word
subtraction [HRS16, paper.tex:217-225]. These are characterizations of the
existing output specifications, with no extra gate or execution interface.
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

/-- The existing explicit overflow bit followed by the actual target operand bits. -/
def outputWord {n : Nat} (state : OverflowRegisters n) : BitVec (n + 1) :=
  BitVec.cons state.2 (BitVec.ofFin state.1.2)

/-- Exact natural value of the complete existing output word, including arbitrary high bit. -/
theorem outputWord_toNat {n : Nat} (state : OverflowRegisters n) :
    (outputWord state).toNat = state.2.toNat * 2 ^ n + state.1.2.val := by
  simp only [outputWord, BitVec.toNat_cons', Nat.shiftLeft_eq, BitVec.toNat_ofFin]

private theorem packed_add_nat (base total : Nat) (bounded : total < 2 * base) (sign : Bool) :
    (sign ^^ decide (base ≤ total)).toNat * base + total % base =
      (sign.toNat * base + total) % (2 * base) := by
  by_cases carry : base ≤ total
  · have lowBound : total - base < base := by omega
    have low : total % base = total - base := by
      calc
        _ = (base + (total - base)) % base :=
          congrArg (fun value => value % base) (by omega)
        _ = _ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt lowBound]
    cases sign with
    | false =>
        simp only [decide_eq_true carry, Bool.false_xor, Bool.toNat_true, Bool.toNat_false,
          Nat.one_mul, Nat.zero_mul, Nat.zero_add, low, Nat.mod_eq_of_lt bounded]
        omega
    | true =>
        simp only [decide_eq_true carry, Bool.xor_self, Bool.toNat_false, Bool.toNat_true,
          Nat.zero_mul, Nat.one_mul, Nat.zero_add, low]
        have expanded : base + total = 2 * base + (total - base) := by omega
        rw [expanded, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : total - base < 2 * base)]
  · have below : total < base := by omega
    cases sign with
    | false =>
        simp only [decide_eq_false carry, Bool.xor_self, Bool.toNat_false, Nat.zero_mul,
          Nat.zero_add, Nat.mod_eq_of_lt below, Nat.mod_eq_of_lt bounded]
    | true =>
        simp only [decide_eq_false carry, Bool.xor_false, Bool.toNat_true, Nat.one_mul,
          Nat.mod_eq_of_lt below, Nat.mod_eq_of_lt (by omega : base + total < 2 * base)]

/-- The complete arbitrary-sign output of actual TTK addition is ordinary finite-word addition. -/
theorem ttkOverflowOutput_word {n : Nat} (state : OverflowRegisters n) :
    outputWord (overflowOutput state) =
      outputWord state + (BitVec.ofFin state.1.1).setWidth (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [outputWord_toNat, BitVec.toNat_add, outputWord_toNat,
    BitVec.toNat_setWidth_of_le (by omega : n ≤ n + 1)]
  change (state.2 ^^ decide (2 ^ n ≤ state.1.1.val + state.1.2.val)).toNat * 2 ^ n +
      (state.1.1.val + state.1.2.val) % 2 ^ n =
    (state.2.toNat * 2 ^ n + state.1.2.val + state.1.1.val) % 2 ^ (n + 1)
  rw [Nat.pow_succ]
  have bounded : state.1.1.val + state.1.2.val < 2 * 2 ^ n := by
    have sourceBound := state.1.1.isLt
    have targetBound := state.1.2.isLt
    omega
  calc
    _ = (state.2.toNat * 2 ^ n + (state.1.1.val + state.1.2.val)) % (2 * 2 ^ n) :=
      packed_add_nat (2 ^ n) _ bounded state.2
    _ = _ := by congr 1 <;> omega

/-- The complete arbitrary-sign output of inverse TTK addition is finite-word subtraction. -/
theorem ttkOverflowSubtractionOutput_word {n : Nat} (state : OverflowRegisters n) :
    outputWord (overflowSubtractionOutput state) =
      outputWord state - (BitVec.ofFin state.1.1).setWidth (n + 1) := by
  have reconstructed :
      outputWord (overflowSubtractionOutput state) +
        (BitVec.ofFin state.1.1).setWidth (n + 1) = outputWord state :=
    (ttkOverflowOutput_word (overflowSubtractionOutput state)).symm.trans
      (congrArg outputWord (overflowOutput_overflowSubtractionOutput n state))
  calc
    _ = (outputWord (overflowSubtractionOutput state) +
          (BitVec.ofFin state.1.1).setWidth (n + 1)) -
        (BitVec.ofFin state.1.1).setWidth (n + 1) :=
      (BitVec.add_sub_cancel _ _).symm
    _ = _ := congrArg (fun value => value -
      (BitVec.ofFin state.1.1).setWidth (n + 1)) reconstructed

/-- The same complete-word equation holds for the actual implemented overflow gate list. -/
theorem ttkOverflow_step_word (n : Nat) (state : OverflowRegisters n) :
    outputWord (EncodedBit.GateSpec.stepList (overflowGates n) state) =
      outputWord state + (BitVec.ofFin state.1.1).setWidth (n + 1) := by
  rw [ttkOverflow_step]
  exact ttkOverflowOutput_word state

/-- The actual inverse elementary gate list gives the complete-word subtraction equation. -/
theorem ttkOverflowSubtraction_step_word (n : Nat) (state : OverflowRegisters n) :
    outputWord (EncodedBit.GateSpec.stepList (overflowSubtractionGates n) state) =
      outputWord state - (BitVec.ofFin state.1.1).setWidth (n + 1) := by
  rw [ttkOverflowSubtraction_step]
  exact ttkOverflowSubtractionOutput_word state

end

end QuantumAlg.MAU.Addition.TTK
