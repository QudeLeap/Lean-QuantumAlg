/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.TTK.Overflow
import all QuantumAlg.Primitives.MAU.Addition.TTK.Resources
import all QuantumAlg.Util.Classical.Arithmetic

/-!
# Exact fixed-width subtraction by reversing TTK addition

The programs reverse the actual self-inverse primitive lists. Their independent
specifications reuse the pure fixed-width subtraction evaluator. This is
integer subtraction modulo `2^n`, with an optional xor-output borrow bit.
HRS explicitly uses the inverse TTK adder for this purpose
[HRS16, paper.tex:217-225; TTK09, qic-loglogaddition-quant.tex:285-318].
-/

namespace QuantumAlg.MAU.Addition.TTK

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec
open ClassicalAlgorithms

/-- Preserve the subtrahend and replace the right word by its wrapped difference. -/
def subtractionOutput {n : Nat} (s : Registers n) : Registers n :=
  (s.1, (SubBorrow.eval (⟨s.2, s.1⟩ : SubBorrow.Input n)).low)

/-- The explicit output xors the mathematical borrow into an arbitrary initial bit. -/
def overflowSubtractionOutput {n : Nat} (s : OverflowRegisters n) : OverflowRegisters n :=
  (subtractionOutput s.1, s.2 ^^ decide (s.1.2.val < s.1.1.val))

/-- The low result is exactly the natural representative of subtraction modulo `2^n`. -/
lemma ttkSubtractionOutput_right_value (n : Nat) (s : Registers n) :
    (subtractionOutput s).2.val = (s.2.val + 2 ^ n - s.1.val) % 2 ^ n := by
  exact SubBorrow.subBorrow_eval_low_eq_wrapping (⟨s.2, s.1⟩ : SubBorrow.Input n)

private lemma subtraction_reconstruct (n : Nat) (s : Registers n) :
    s.2.val + (decide (s.2.val < s.1.val)).toNat * 2 ^ n =
      s.1.val + (subtractionOutput s).2.val := by
  exact SubBorrow.subBorrow_eval_reconstruct (⟨s.2, s.1⟩ : SubBorrow.Input n)

private lemma lowOutput_subtractionOutput (n : Nat) (s : Registers n) :
    lowOutput (subtractionOutput s) = s := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (s.1.val + (subtractionOutput s).2.val) % 2 ^ n = s.2.val
    rw [← subtraction_reconstruct]
    cases decide (s.2.val < s.1.val) <;> simp [Nat.mod_eq_of_lt s.2.isLt]

private lemma carry_subtractionOutput (n : Nat) (s : Registers n) :
    decide (2 ^ n ≤ (subtractionOutput s).1.val + (subtractionOutput s).2.val) =
      decide (s.2.val < s.1.val) := by
  change decide (2 ^ n ≤ s.1.val + (subtractionOutput s).2.val) = _
  rw [← subtraction_reconstruct]
  cases decide (s.2.val < s.1.val) with
  | false =>
      simpa only [Bool.toNat_false, Nat.zero_mul, Nat.add_zero] using
        decide_eq_false (Nat.not_le_of_gt s.2.isLt)
  | true =>
      simpa only [Bool.toNat_true, Nat.one_mul] using
        decide_eq_true (by omega : 2 ^ n ≤ s.2.val + 2 ^ n)

private lemma overflowOutput_overflowSubtractionOutput
    (n : Nat) (s : OverflowRegisters n) :
    overflowOutput (overflowSubtractionOutput s) = s := by
  apply Prod.ext
  · exact lowOutput_subtractionOutput n s.1
  · change ((s.2 ^^ decide (s.1.2.val < s.1.1.val)) ^^
      decide (2 ^ n ≤ (subtractionOutput s.1).1.val +
        (subtractionOutput s.1).2.val)) = s.2
    rw [carry_subtractionOutput]
    simp

/-- The actual inverse low-word primitive sequence, with no extra workspace. -/
def subtractionGates (n : Nat) : List (EncodedBit.GateSpec (encoding n)) :=
  (lowRippleGates n).reverse

/-- Compile the inverse sequence on the same two operand words. -/
def subtractionProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (subtractionGates n)

/-- The actual inverse sequence on two operand words and the explicit borrow output. -/
def overflowSubtractionGates (n : Nat) :
    List (EncodedBit.GateSpec (overflowEncoding n)) :=
  (overflowGates n).reverse

/-- Compile subtraction with the explicit borrow output on exactly `2n+1` qubits. -/
def overflowSubtractionProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (overflowEncoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (overflowSubtractionGates n)

/-- Reversing the real low-word gates implements subtraction at every width. -/
lemma ttkSubtraction_step (n : Nat) (s : Registers n) :
    stepList (subtractionGates n) s = subtractionOutput s := by
  have h := stepList_reverse_stepList (lowRippleGates n) (subtractionOutput s)
  rw [ttkLowRipple_step n (subtractionOutput s), lowOutput_subtractionOutput] at h
  exact h

/-- Reversing the real overflow gates computes subtraction and xor-output borrow. -/
lemma ttkOverflowSubtraction_step (n : Nat) (s : OverflowRegisters n) :
    stepList (overflowSubtractionGates n) s = overflowSubtractionOutput s := by
  have h := stepList_reverse_stepList (overflowGates n) (overflowSubtractionOutput s)
  rw [ttkOverflow_step n (overflowSubtractionOutput s),
    overflowOutput_overflowSubtractionOutput] at h
  exact h

/-- Exact basis amplitudes realize subtraction, including relative phases. -/
lemma ttkSubtraction_realizes (n : Nat) :
    UnitaryCircuit.Realizes (encoding n) (subtractionProgram n) environment subtractionOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (subtractionGates n) (ttkSubtraction_step n) environment

/-- Exact subtraction with arbitrary initial borrow output has no input restriction. -/
lemma ttkOverflowSubtraction_realizes (n : Nat) :
    UnitaryCircuit.Realizes (overflowEncoding n) (overflowSubtractionProgram n) environment
      overflowSubtractionOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (overflowSubtractionGates n) (ttkOverflowSubtraction_step n) environment

/-- Reversal preserves every actual native count, so the independent low-word
resource formulas apply unchanged. -/
lemma ttkSubtraction_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (subtractionProgram n).eventCost =
      ResourcePool.count focus (lowRippleProgram n).eventCost := by
  simp only [subtractionProgram, subtractionGates, lowRippleProgram,
    programList_event_count_eq_sum_eventMultiplicity, List.map_reverse, List.sum_reverse]

/-- Borrow-output subtraction has exactly the native counts of overflow addition. -/
lemma ttkOverflowSubtraction_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (overflowSubtractionProgram n).eventCost =
      ResourcePool.count focus (overflowProgram n).eventCost := by
  simp only [overflowSubtractionProgram, overflowSubtractionGates, overflowProgram,
    programList_event_count_eq_sum_eventMultiplicity, List.map_reverse, List.sum_reverse]

/-- Serial subtraction has the same independent all-width event and depth budget. -/
lemma ttkSubtraction_serial_resources (n : Nat) :
    (subtractionProgram n).eventCost.card = n + 4 * (n - 1) + 2 * (n - 2) ∧
      (subtractionProgram n).evaluatedEventDepth (fun _ => 1) =
        n + 4 * (n - 1) + 2 * (n - 2) := by
  constructor
  · simpa only [subtractionProgram, subtractionGates, lowRippleProgram,
      programList_eventCost_card, List.length_reverse] using ttkLowRipple_event_count n
  · simpa only [subtractionProgram, subtractionGates, lowRippleProgram,
      programList_evaluatedEventDepth_unit, List.length_reverse] using ttkLowRipple_serial_depth n

/-- The borrow-output inverse retains the same all-width serial overflow budget. -/
lemma ttkOverflowSubtraction_serial_resources (n : Nat) :
    (overflowSubtractionProgram n).eventCost.card =
        n + 4 * (n - 1) + 2 * (n - 2) +
          (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) ∧
      (overflowSubtractionProgram n).evaluatedEventDepth (fun _ => 1) =
        n + 4 * (n - 1) + 2 * (n - 2) +
          (if 2 ≤ n then 1 else 0) + (if n = 0 then 0 else 1) := by
  constructor
  · simpa only [overflowSubtractionProgram, overflowSubtractionGates, overflowProgram,
      programList_eventCost_card, List.length_reverse] using ttkOverflow_event_count n
  · simpa only [overflowSubtractionProgram, overflowSubtractionGates, overflowProgram,
      programList_evaluatedEventDepth_unit, List.length_reverse] using ttkOverflow_serial_depth n

end

end QuantumAlg.MAU.Addition.TTK
