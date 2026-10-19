/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Measurement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Selected
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Born
import all QuantumAlg.Core.Execution.Basis.Seeded.Record

/-!
# Complete selected Shor execution records and every reference matrix entry

Arbitrary weights distinguish original stores, hidden states, histories and
actual branch paths. Each block has its own actual source amplitude; no such
record coordinate is summed away as an input assumption.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma record_unitary_entry {R Reference : Register}
    (seed : R.Index) (block : DensityOperator (Register.prod R Reference))
    (operator : UnitaryOperator R) (left right : R.Index)
    (leftRef rightRef : Reference.Index)
    (entries : ∀ row column,
      block.matrix (row, leftRef) (column, rightRef) =
        if row = seed ∧ column = seed then
          block.matrix (seed, leftRef) (seed, rightRef) else 0) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference)) block).matrix
        (left, leftRef) (right, rightRef) =
      operator left seed * block.matrix (seed, leftRef) (seed, rightRef) *
        star (operator right seed) := by
  generalize block.matrix (seed, leftRef) (seed, rightRef) = coefficient at entries ⊢
  rw [DensityOperator.localUnitary_block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
    entries, ite_and, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)
  (sameWires : base.quantumWires = (layout N).wires)

/-- Every actual selected record retains its own original zero/reference coefficient. -/
lemma selected_seed_record_entry
    (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds (Storage.context base N).quantumLayout.zeroLabel state)
    (weight : Store (Storage.context base N) ×
      ((executionModel N).HiddenState ×
        (History × (selected base N sameWires parameter).Path)) → ℂ)
    (left right : (Storage.context base N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.weightedMatrixEntry
      ((selected base N sameWires parameter).execute (environment input) Reference state)
      weight (left, leftRef) (right, rightRef) =
      ∑ original : Store (Storage.context base N) ×
        ((executionModel N).HiddenState × History),
        weight (original.1, (original.2.1, (original.2.2,
          ⟨original.1.read (Storage.liftInput base N parameter), ()⟩))) *
        ((DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
          (selectedBase (original.1.read (Storage.liftInput base N parameter)))).normalized
            (basisEquiv N ((Storage.quantumWires base N).trans sameWires) left) *
          (state.block original).matrix
            ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
            ((Storage.context base N).quantumLayout.zeroLabel, rightRef) *
          star ((DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
            (selectedBase (original.1.read (Storage.liftInput base N parameter)))).normalized
              (basisEquiv N ((Storage.quantumWires base N).trans sameWires) right))) := by
  rw [selected_execute, ExecutionState.weightedMatrixEntry_mapClassical]
  unfold ExecutionState.weightedMatrixEntry
  apply Finset.sum_congr rfl
  intro original _
  simp only [ExecutionState.applyUnitary_block]
  have entries (row column : (Storage.context base N).register.Index) :
      (state.block original).matrix (row, leftRef) (column, rightRef) =
        if row = (Storage.context base N).quantumLayout.zeroLabel ∧
          column = (Storage.context base N).quantumLayout.zeroLabel then
          (state.block original).matrix
            ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
            ((Storage.context base N).quantumLayout.zeroLabel, rightRef)
        else 0 := by
    by_cases supported : row = (Storage.context base N).quantumLayout.zeroLabel ∧
        column = (Storage.context base N).quantumLayout.zeroLabel
    · obtain ⟨rfl, rfl⟩ := supported
      exact (if_pos ⟨rfl, rfl⟩).symm
    · exact (BasisSeeded.block_entry_zero (Storage.context base N).quantumLayout.zeroLabel
        state seeded original row column leftRef rightRef supported).trans
          (if_neg supported).symm
  refine congrArg
    (fun coefficient : ℂ => weight
      (original.1, (original.2.1, (original.2.2,
        ⟨original.1.read (Storage.liftInput base N parameter), ()⟩))) * coefficient)
    ((record_unitary_entry (Storage.context base N).quantumLayout.zeroLabel
      (state.block original)
      ((member N ((Storage.quantumWires base N).trans sameWires)
        (original.1.read (Storage.liftInput base N parameter))).matrix
          (environment input).quantum)
      left right leftRef rightRef entries).trans ?_)
  rw [member_zero_amplitude, member_zero_amplitude]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
