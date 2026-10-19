/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Complement
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# HRS incrementer with a restored borrowed word

The actual program performs two reversed TTK additions, complementing the
borrowed word after each subtraction. Since `g + complement g = 2^n - 1`,
the target increases by one modulo `2^n` and the borrowed word is restored
[HRS16, paper.tex:219-224].

This internal component has `n` target bits and `n` borrowed bits. It is not
the final HRS constant adder with one external dirty bit. There is no input
restriction on the borrowed word, and exact realization retains relative
phases across every pair of borrowed and target basis labels.
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.GateSpec
open ClassicalAlgorithms

/-- Increment the target modulo `2^n` and preserve the borrowed word. -/
def borrowedIncrementOutput {n : Nat} (state : TTK.Registers n) : TTK.Registers n :=
  (state.1, ⟨(state.2.val + 1) % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩)

/-- Two actual inverse TTK lists interleaved with literal borrowed-word X lists. -/
def borrowedIncrementGates (n : Nat) : List (EncodedBit.GateSpec (TTK.encoding n)) :=
  TTK.subtractionGates n ++ complementGates n ++
    TTK.subtractionGates n ++ complementGates n

/-- Compile the HRS incrementer on its exact two-word interface. -/
def borrowedIncrementProgram (n : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (TTK.encoding n).width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (borrowedIncrementGates n)

private lemma two_subtractions (n : Nat) (state : TTK.Registers n) :
    complementOutput (TTK.subtractionOutput
      (complementOutput (TTK.subtractionOutput state))) =
        borrowedIncrementOutput state := by
  let first := TTK.subtractionOutput state
  let second := TTK.subtractionOutput (complementOutput first)
  have hfirst : state.2.val +
      (decide (state.2.val < state.1.val)).toNat * 2 ^ n =
        state.1.val + first.2.val := by
    exact SubBorrow.subBorrow_eval_reconstruct
      (⟨state.2, state.1⟩ : SubBorrow.Input n)
  have hsecond : first.2.val +
      (decide (first.2.val < (complementWord state.1).val)).toNat * 2 ^ n =
        (complementWord state.1).val + second.2.val := by
    exact SubBorrow.subBorrow_eval_reconstruct
      (⟨first.2, complementWord state.1⟩ : SubBorrow.Input n)
  have hsum := hrsComplementWord_sum n state.1
  have hbalance : state.2.val + 1 +
      ((decide (state.2.val < state.1.val)).toNat * 2 ^ n +
        (decide (first.2.val < (complementWord state.1).val)).toNat * 2 ^ n) =
          2 ^ n + second.2.val := by
    omega
  have hmod := congrArg (fun value : Nat => value % 2 ^ n) hbalance
  have htarget : second.2.val = (state.2.val + 1) % 2 ^ n := by
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
      Nat.zero_mod, Nat.add_zero, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt second.2.isLt] using hmod.symm
  apply Prod.ext
  · exact hrsComplementWord_involutive n state.1
  · apply Fin.ext
    exact htarget

/-- The literal gate list restores every borrowed word and increments the target. -/
lemma hrsBorrowedIncrement_step (n : Nat) (state : TTK.Registers n) :
    stepList (borrowedIncrementGates n) state = borrowedIncrementOutput state := by
  simp only [borrowedIncrementGates, stepList_append,
    TTK.ttkSubtraction_step, hrsComplement_step]
  exact two_subtractions n state

/-- Exact all-input realization includes all borrowed-word relative phases. -/
lemma hrsBorrowedIncrement_realizes (n : Nat) :
    UnitaryCircuit.Realizes (TTK.encoding n) (borrowedIncrementProgram n) environment
      borrowedIncrementOutput :=
  realizesList_congrStep (QubitLayout.canonical _) .empty
    (borrowedIncrementGates n) (hrsBorrowedIncrement_step n) environment

/-- An untouched reference can accompany every input without changing the
exact action. Linearity therefore retains arbitrary joint superpositions. -/
lemma hrsBorrowedIncrement_realizes_with_reference (n : Nat) {Reference : Type}
    (reference : BinaryLabelEncoding Reference) :
    UnitaryCircuit.Realizes
      (layout := QubitLayout.canonical ((TTK.encoding n).width + reference.width))
      (BinaryLabelEncoding.prod (TTK.encoding n) reference)
      (UnitaryCircuit.onBinaryPrefix reference.width (borrowedIncrementProgram n)) environment
      (fun state : TTK.Registers n × Reference =>
        (borrowedIncrementOutput state.1, state.2)) :=
  UnitaryCircuit.Realizes.onBinaryPrefix (right := reference)
    (hrsBorrowedIncrement_realizes n)

/-- Every native count is derived from the four executed primitive lists. -/
lemma hrsBorrowedIncrement_native_count (n : Nat)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (borrowedIncrementProgram n).eventCost =
      2 * ResourcePool.count focus (TTK.lowRippleProgram n).eventCost +
        2 * (n *
          (if (.gate .singleQubit :
            Resource.Event (.quantum AlgorithmGate.model .empty)) = focus then 1 else 0)) := by
  have h : ResourcePool.count focus (borrowedIncrementProgram n).eventCost =
      ResourcePool.count focus (TTK.subtractionProgram n).eventCost +
        ResourcePool.count focus (complementProgram n).eventCost +
        ResourcePool.count focus (TTK.subtractionProgram n).eventCost +
        ResourcePool.count focus (complementProgram n).eventCost := by
    simp only [borrowedIncrementProgram, borrowedIncrementGates,
      TTK.subtractionProgram, complementProgram,
      programList_event_count_eq_sum_eventMultiplicity, List.map_append, List.sum_append]
  rw [h, TTK.ttkSubtraction_native_count, hrsComplement_native_count]
  omega

/-- Exactly two X gates are executed for every borrowed bit. -/
lemma hrsBorrowedIncrement_x_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (borrowedIncrementProgram n).eventCost =
      2 * n := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_native_count]
  simp

/-- The two literal TTK inverse lists determine the full CNOT count. -/
lemma hrsBorrowedIncrement_cnot_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (borrowedIncrementProgram n).eventCost =
      2 * (n + 2 * (n - 1) + 2 * (n - 2)) := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_cnot_count]
  simp

/-- The Toffoli formula follows from the actual all-width TTK implementation. -/
lemma hrsBorrowedIncrement_toffoli_count (n : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (borrowedIncrementProgram n).eventCost =
      4 * (n - 1) := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_toffoli_count]
  simp [← Nat.mul_assoc]

/-- Event count of the actual serial program, including widths zero and one. -/
lemma hrsBorrowedIncrement_event_count (n : Nat) :
    (borrowedIncrementProgram n).eventCost.card =
      4 * n + 8 * (n - 1) + 4 * (n - 2) := by
  have h : (borrowedIncrementProgram n).eventCost.card =
      2 * (TTK.subtractionProgram n).eventCost.card +
        2 * (complementProgram n).eventCost.card := by
    simp only [borrowedIncrementProgram, borrowedIncrementGates,
      TTK.subtractionProgram, complementProgram, programList_eventCost_card,
      List.length_append]
    omega
  rw [h, (TTK.ttkSubtraction_serial_resources n).1,
    (hrsComplement_serial_resources n).1]
  omega

/-- Unit-duration depth of the executed serial gate list, without a parallel
rescheduling claim. -/
lemma hrsBorrowedIncrement_serial_depth (n : Nat) :
    (borrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
      4 * n + 8 * (n - 1) + 4 * (n - 2) := by
  calc
    (borrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
        (borrowedIncrementProgram n).eventCost.card := by
          simp only [borrowedIncrementProgram, programList_evaluatedEventDepth_unit,
            programList_eventCost_card]
    _ = _ := hrsBorrowedIncrement_event_count n

/-- The internal incrementer uses its target and borrowed words only. -/
lemma hrsBorrowedIncrement_interface (n : Nat) :
    (TTK.encoding n).width = 2 * n ∧
      (QubitLayout.canonical (TTK.encoding n).width).systemIdx =
        List.range (2 * n) := by
  constructor
  · exact TTK.ttkEncoding_width n
  · rw [TTK.ttkEncoding_width]
    exact QubitLayout.canonical_systemIdx (2 * n)

end

end QuantumAlg.MAU.Addition.HRS
