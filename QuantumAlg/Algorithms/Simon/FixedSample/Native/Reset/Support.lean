/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Matrix
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# Complete zero support after the two real reset batches

Each measured half becomes zero in every complete store/reference block.
The second half's correction has identity action on the first half and
therefore preserves its established zero support. The two physical halves
cover the original bank, including the empty-bank case.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {allowAllocation : Bool} {oracles : OracleModel}
  {environment : (nativeModel oracles).Environment}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- Zero in both actual physical halves is exactly zero in the complete bank. -/
lemma zero_iff_halves (basis : (context base noQuantum n count).register.Index) :
    basis = (context base noQuantum n count).quantumLayout.zeroLabel ↔
      selectedBasis base noQuantum n count 0 basis = (Gate.HadamardLayer.layout n).zeroLabel ∧
      selectedBasis base noQuantum n count 1 basis = (Gate.HadamardLayer.layout n).zeroLabel := by
  constructor
  · intro same
    subst basis
    constructor <;> funext index <;> apply Fin.ext <;> rfl
  · intro zero
    funext wire
    obtain ⟨half, index, rfl⟩ := positions_cover base noQuantum n count wire
    apply Fin.ext
    have selected : selectedBasis base noQuantum n count half basis =
        (Gate.HadamardLayer.layout n).zeroLabel := by
      fin_cases half
      · exact zero.1
      · exact zero.2
    exact congrArg (fun value => (value index).val) selected

/-- An actual measured batch clears its half separately in every complete final store. -/
lemma batch_zero (half : Fin 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (stored : Store (context base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index)
    (outside : selectedBasis base noQuantum n count half left ≠
      (Gate.HadamardLayer.layout n).zeroLabel ∨
      selectedBasis base noQuantum n count half right ≠ (Gate.HadamardLayer.layout n).zeroLabel) :
    (((batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix (left, leftRef) (right, rightRef) =
        0 := by
  rw [batch_store_entry]
  apply Finset.sum_eq_zero
  intro column _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro row _
  by_cases agree : Circuit.measurementLabelsAgree (readouts base noQuantum n count half)
      row column
  · rw [if_pos agree, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro original _
    by_cases sameStore : writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half original row = stored
    · rw [if_pos sameStore]
      have columnStore : writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          base noQuantum n count half original column = stored :=
        (writtenStore_equal (allowAllocation := allowAllocation) (oracles := oracles)
          base noQuantum n count half original row column agree).symm.trans sameStore
      rcases outside with leftOutside | rightOutside
      · have absent := correction_written_column
          (environment := environment) (allowAllocation := allowAllocation)
          (oracles := oracles) base noQuantum n count half original left row
        rw [sameStore, if_neg leftOutside, zero_mul] at absent
        rw [absent, zero_mul, zero_mul]
      · have absent := correction_written_column
          (environment := environment) (allowAllocation := allowAllocation)
          (oracles := oracles) base noQuantum n count half original right column
        rw [columnStore, if_neg rightOutside, zero_mul] at absent
        rw [absent, star_zero, mul_zero]
    · rw [if_neg sameStore, mul_zero, zero_mul]
  · rw [if_neg agree, mul_zero, zero_mul]

private lemma first_not_selected_second (index : Fin n) :
    positions base noQuantum n count 0 index ∉
      Finset.univ.map (positions base noQuantum n count 1) := by
  intro present
  obtain ⟨other, _, same⟩ := Finset.mem_map.mp present
  exact positions_separate base noQuantum n count index other same.symm

/-- The second placement's complementary coordinates retain the entire first physical half. -/
lemma spectators_first (left right : (context base noQuantum n count).register.Index)
    (same : spectators base noQuantum n count 1 left =
      spectators base noQuantum n count 1 right) :
    selectedBasis base noQuantum n count 0 left = selectedBasis base noQuantum n count 0 right :=
      by
  funext index
  apply Fin.ext
  have physical := congrArg Fin.val (congrFun same
    ⟨positions base noQuantum n count 0 index,
      Finset.mem_compl.mpr (first_not_selected_second base noQuantum n count index)⟩)
  simpa only [selectedBasis, UnitaryCircuit.basisAt_val, spectators,
    QuantumLayout.restrictComplementBasis, QuantumLayout.restrictSelectedBasis] using physical

/-- The second real batch preserves the first half's complete store/reference zero support. -/
lemma second_preserves_first
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (wasZero : ∀ (original : Store (context base noQuantum n count))
      (row column : (context base noQuantum n count).register.Index)
      (rowRef columnRef : Reference.Index),
      (selectedBasis base noQuantum n count 0 row ≠ (Gate.HadamardLayer.layout n).zeroLabel ∨
        selectedBasis base noQuantum n count 0 column ≠ (Gate.HadamardLayer.layout n).zeroLabel) →
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (row, rowRef) (column, columnRef) = 0)
    (stored : Store (context base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index)
    (outside : selectedBasis base noQuantum n count 0 left ≠
      (Gate.HadamardLayer.layout n).zeroLabel ∨
      selectedBasis base noQuantum n count 0 right ≠ (Gate.HadamardLayer.layout n).zeroLabel) :
    (((batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count 1).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix (left, leftRef) (right, rightRef) =
        0 := by
  rw [batch_store_entry]
  apply Finset.sum_eq_zero
  intro column _
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro row _
  by_cases sameLeft : spectators base noQuantum n count 1 left =
      spectators base noQuantum n count 1 row
  · by_cases sameRight : spectators base noQuantum n count 1 right =
        spectators base noQuantum n count 1 column
    · have absent (original : Store (context base noQuantum n count)) :=
        wasZero original row column leftRef rightRef (by
          rcases outside with leftOutside | rightOutside
          · exact Or.inl (fun zero => leftOutside
              ((spectators_first base noQuantum n count left row sameLeft).trans zero))
          · exact Or.inr (fun zero => rightOutside
              ((spectators_first base noQuantum n count right column sameRight).trans zero)))
      simp only [absent, ite_self, Finset.sum_const_zero, mul_zero, zero_mul]
    · have absent : (correction (oracles := oracles) base noQuantum n count 1
          (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
            environment.quantum right column =
          0 := by
        rw [correction_entry, if_neg sameRight, mul_zero]
      rw [absent, star_zero, mul_zero]
  · have absent : (correction (oracles := oracles) base noQuantum n count 1
        (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
          environment.quantum left row = 0 :=
        by
      rw [correction_entry, if_neg sameLeft, mul_zero]
    rw [absent, zero_mul, zero_mul]

/-- Both actual batches establish the original zero bank in every final store/reference block. -/
lemma code_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel
      ((code (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count).execute environment Reference state) := by
  intro stored left right leftRef rightRef
  by_cases zero : left = (context base noQuantum n count).quantumLayout.zeroLabel ∧
      right = (context base noQuantum n count).quantumLayout.zeroLabel
  · obtain ⟨rfl, rfl⟩ := zero
    exact (if_pos ⟨rfl, rfl⟩).symm
  · rw [if_neg zero]
    have reassociate := congrArg
      (fun density : DensityOperator
        (Register.prod (context base noQuantum n count).register Reference) =>
          density.matrix (left, leftRef) (right, rightRef))
      (Circuit.seq_store_marginal (environment := environment)
        (batch (allowAllocation := allowAllocation) (oracles := oracles)
          base noQuantum n count 0)
        (batch (allowAllocation := allowAllocation) (oracles := oracles)
          base noQuantum n count 1) state stored)
    refine reassociate.trans ?_
    by_cases first : selectedBasis base noQuantum n count 0 left =
        (Gate.HadamardLayer.layout n).zeroLabel ∧
        selectedBasis base noQuantum n count 0 right = (Gate.HadamardLayer.layout n).zeroLabel
    · apply batch_zero base noQuantum n count 1 _ stored left right leftRef rightRef
      by_contra absent
      push Not at absent
      exact zero ⟨(zero_iff_halves base noQuantum n count left).mpr ⟨first.1, absent.1⟩,
        (zero_iff_halves base noQuantum n count right).mpr ⟨first.2, absent.2⟩⟩
    · apply second_preserves_first base noQuantum n count
        ((batch (allowAllocation := allowAllocation) (oracles := oracles)
          base noQuantum n count 0).execute environment Reference state)
        (fun original row column rowRef columnRef outside =>
          batch_zero base noQuantum n count 0 state original row column rowRef columnRef outside)
        stored left right leftRef rightRef
      exact not_and_or.mp first

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
