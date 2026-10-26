/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Carry.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Sparse.Readout
import all QuantumAlg.Util.Nat.FixedWidth.Modular.NearPower.Carry

/-!
# Canonical arithmetic and actual clean-flag restoration

Both inputs are original quantum words with arbitrary canonical values,
including zero. The actual sum, sparse carry, controlled correction and
operand comparison retain the addend and restore the original clean flag.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

/-- The mathematical modular sum in the original physical word. -/
def modularSumWord (left right : Word) : Word :=
  ⟨(left.val + right.val) % modulus,
    (Nat.mod_lt _ modulus_positive).trans modulus_lt_capacity⟩

private lemma carry_flag_step (state : Registers) :
    complementCarryStep state =
      (state.1, state.2 ^^ decide (modulus ≤ state.1.2.val)) := by
  rw [complementCarry_step_eq]
  by_cases selected : modulus ≤ state.1.2.val
  · rw [if_pos selected, decide_eq_true selected, Bool.xor_true]
    rfl
  · rw [if_neg selected, decide_eq_false selected, Bool.xor_false]

private lemma addition_step_readout (state : Registers) :
    additionStep state = MAU.Addition.TTK.comparisonOutput
      (sparseComplementStep (complementCarryStep (MAU.Addition.TTK.overflowOutput state))) :=
  rfl

/-- Exact canonical modular addition, with the supplied clean flag actually restored. -/
lemma addition_clean_canonical (left right : Word)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right) :
    additionStep ((left, right), false) = ((left, modularSumWord left right), false) := by
  have leftBound : left.val < modulus := leftCanonical
  have rightBound : right.val < modulus := rightCanonical
  have sumBound : left.val + right.val < 2 * modulus := by omega
  let lowWord : Word :=
    ⟨(left.val + right.val) % capacity, Nat.mod_lt _ (Nat.two_pow_pos width)⟩
  let wrap : Bool := decide (modulus ≤ left.val + right.val)
  have afterCarry :
      complementCarryStep (MAU.Addition.TTK.overflowOutput ((left, right), false)) =
        ((left, lowWord), wrap) := by
    rw [carry_flag_step]
    change ((left, lowWord),
      (false ^^ decide (capacity ≤ left.val + right.val)) ^^
        decide (modulus ≤ (left.val + right.val) % capacity)) = ((left, lowWord), wrap)
    rw [Bool.false_xor,
      Nat.FixedWidth.NearPower.full_carry_xor_eq_wrap modulus_add_complement sumBound]
  let corrected := complementWordStep ((left, lowWord), wrap)
  have correctedAddend : corrected.1.1 = left := by
    dsimp only [corrected, complementWordStep]
    split <;> rfl
  have correctedFlag : corrected.2 = wrap := by
    dsimp only [corrected, complementWordStep]
    split <;> rfl
  have correctedWord : corrected.1.2 = modularSumWord left right := by
    apply Fin.ext
    have arithmetic := Nat.FixedWidth.NearPower.correctedLow_eq_mod
      modulus_add_complement sumBound
    simp only [Nat.FixedWidth.NearPower.correctedLow,
      Nat.FixedWidth.NearPower.full_carry_wrap_iff modulus_add_complement] at arithmetic
    by_cases selected : modulus ≤ left.val + right.val
    · rw [if_pos selected] at arithmetic
      change (complementWordStep ((left, lowWord), wrap)).1.2.val = _
      dsimp only [complementWordStep, wrap]
      rw [decide_eq_true selected]
      exact arithmetic
    · rw [if_neg selected] at arithmetic
      change (complementWordStep ((left, lowWord), wrap)).1.2.val = _
      dsimp only [complementWordStep, wrap]
      rw [decide_eq_false selected]
      exact arithmetic
  have afterSparse :
      sparseComplementStep (complementCarryStep
        (MAU.Addition.TTK.overflowOutput ((left, right), false))) = corrected :=
    (congrArg sparseComplementStep afterCarry).trans
      (sparseComplementStep_eq_wordStep ((left, lowWord), wrap))
  refine (addition_step_readout ((left, right), false)).trans ?_
  refine (congrArg MAU.Addition.TTK.comparisonOutput afterSparse).trans ?_
  apply Prod.ext
  · apply Prod.ext
    · exact correctedAddend
    · exact correctedWord
  · change (corrected.2 ^^ decide (corrected.1.2.val < corrected.1.1.val)) = false
    rw [correctedFlag, correctedWord, correctedAddend]
    have cleanup := Nat.FixedWidth.NearPower.add_wrap_xor_cleanup
      (left := left.val) rightBound
    rw [Nat.FixedWidth.NearPower.reduceOnce_eq_mod sumBound] at cleanup
    exact cleanup

/-- Literal instructions realize the same canonical operation on every admitted input label. -/
lemma additionGates_clean_canonical (left right : Word)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right) :
    stepList additionGates ((left, right), false) =
      ((left, modularSumWord left right), false) := by
  rw [additionGates_step]
  exact addition_clean_canonical left right leftCanonical rightCanonical

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
