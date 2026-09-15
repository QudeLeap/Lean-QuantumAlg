/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.HRS.Complement

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
def borrowedIncrementProgram (n : Nat) : UnitaryCircuit (Qubits (TTK.encoding n).width) :=
  programList (borrowedIncrementGates n)

private theorem two_subtractions (n : Nat) (state : TTK.Registers n) :
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
theorem hrsBorrowedIncrement_step (n : Nat) (state : TTK.Registers n) :
    stepList (borrowedIncrementGates n) state = borrowedIncrementOutput state := by
  simp only [borrowedIncrementGates, stepList_append,
    TTK.ttkSubtraction_step, hrsComplement_step]
  exact two_subtractions n state

/-- Exact all-input realization includes all borrowed-word relative phases. -/
theorem hrsBorrowedIncrement_realizes (n : Nat) :
    UnitaryCircuit.Realizes (TTK.encoding n) (borrowedIncrementProgram n)
      borrowedIncrementOutput :=
  realizesList_congrStep (borrowedIncrementGates n) (hrsBorrowedIncrement_step n)

/-- An untouched reference can accompany every input without changing the
exact action. Linearity therefore retains arbitrary joint superpositions. -/
theorem hrsBorrowedIncrement_realizes_with_reference (n : Nat) {Reference : Type}
    (reference : BinaryLabelEncoding Reference) :
    UnitaryCircuit.Realizes (BinaryLabelEncoding.prod (TTK.encoding n) reference)
      (UnitaryCircuit.prodLeft (n := reference.width) (borrowedIncrementProgram n))
      (fun state : TTK.Registers n × Reference =>
        (borrowedIncrementOutput state.1, state.2)) :=
  (hrsBorrowedIncrement_realizes n).prodLeft

/-- Every native count is derived from the four executed primitive lists. -/
theorem hrsBorrowedIncrement_native_count (n : Nat) (focus : Resource.Event .quantum) :
    ResourcePool.count focus (borrowedIncrementProgram n).eventCost =
      2 * ResourcePool.count focus (TTK.lowRippleProgram n).eventCost +
        2 * (n *
          (if (.gate (.builtin "x") : Resource.Event .quantum) = focus then 1 else 0)) := by
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
theorem hrsBorrowedIncrement_x_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "x")) (borrowedIncrementProgram n).eventCost =
      2 * n := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_native_count]
  simp [Resource.GateLabel.builtin]

/-- The two literal TTK inverse lists determine the full CNOT count. -/
theorem hrsBorrowedIncrement_cnot_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "cnot")) (borrowedIncrementProgram n).eventCost =
      2 * (n + 2 * (n - 1) + 2 * (n - 2)) := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_cnot_count]
  simp [Resource.GateLabel.builtin]

/-- The Toffoli formula follows from the actual all-width TTK implementation. -/
theorem hrsBorrowedIncrement_toffoli_count (n : Nat) :
    ResourcePool.count (.gate (.builtin "toffoli")) (borrowedIncrementProgram n).eventCost =
      4 * (n - 1) := by
  rw [hrsBorrowedIncrement_native_count, TTK.ttkLowRipple_toffoli_count]
  simp [Resource.GateLabel.builtin, ← Nat.mul_assoc]

/-- Event count of the actual serial program, including widths zero and one. -/
theorem hrsBorrowedIncrement_event_count (n : Nat) :
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
theorem hrsBorrowedIncrement_serial_depth (n : Nat) :
    (borrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
      4 * n + 8 * (n - 1) + 4 * (n - 2) := by
  calc
    (borrowedIncrementProgram n).evaluatedEventDepth (fun _ => 1) =
        (borrowedIncrementProgram n).eventCost.card := by
          simp only [borrowedIncrementProgram, programList_evaluatedEventDepth_unit,
            programList_eventCost_card]
    _ = _ := hrsBorrowedIncrement_event_count n

/-- The internal incrementer uses its target and borrowed words only. -/
theorem hrsBorrowedIncrement_interface (n : Nat) :
    (TTK.encoding n).width = 2 * n ∧
      (borrowedIncrementProgram n).physical_idx ⊆ List.range (2 * n) := by
  constructor
  · exact TTK.ttkEncoding_width n
  · simpa only [borrowedIncrementProgram, TTK.ttkEncoding_width] using
      programList_physical_idx_subset_range (borrowedIncrementGates n)

end

end QuantumAlg.MAU.Addition.HRS
