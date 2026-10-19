/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction.Matrix
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Exact partial-bank correction and measured store blocks

The selected operator acts on its actual n physical wires and has an identity
factor on the complete complement. The cells written by measurement select
precisely the X column that clears those wires. These equations retain both
arbitrary reference coordinates and every complete classical-store block.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {allowAllocation : Bool} {oracles : OracleModel}
  {environment : (nativeModel oracles).Environment}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- The selected half in the original physical wire order. -/
def selectedBasis (half : Fin 2) (basis : (context base noQuantum n count).register.Index) :
    (Gate.HadamardLayer.layout n).Basis :=
  UnitaryCircuit.basisAt (Gate.HadamardLayer.layout n)
    (context base noQuantum n count).quantumLayout (positions base noQuantum n count half)
    (dimensions base noQuantum n count half) basis

/-- The full complementary physical subsystem, including every coherence. -/
def spectators (half : Fin 2) (basis : (context base noQuantum n count).register.Index) :=
  (context base noQuantum n count).quantumLayout.restrictComplementBasis
    (Finset.univ.map (positions base noQuantum n count half)) basis

/-- The placed correction keeps the exact identity factor on the physical complement. -/
lemma correction_entry (half : Fin 2)
    (value : CShape.Value (.fixedVector n (.finite 2)))
    (row column : (context base noQuantum n count).register.Index) :
    (correction (oracles := oracles) base noQuantum n count half value).matrix environment.quantum
      row column =
      (ZReset.BankParallel.Correction.layer oracles n (QubitReadouts.mask value)).matrix
        environment.quantum
        (selectedBasis base noQuantum n count half row)
        (selectedBasis base noQuantum n count half column) *
      (if spectators base noQuantum n count half row =
        spectators base noQuantum n count half column then 1 else 0) := by
  rw [correction, UnitaryCircuit.placeAt_matrix, UnitaryCircuit.operatorAt,
    QuantumLayout.Embedding.liftOperator_entry]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
  have readBasis (basis : (context base noQuantum n count).register.Index) :
      (QuantumLayout.relabelBasis (Gate.HadamardLayer.layout n)
        (UnitaryCircuit.addressPermutation (Gate.HadamardLayer.layout n)
          (context base noQuantum n count).quantumLayout
          (positions base noQuantum n count half)).toEmbedding).symm
        ((UnitaryCircuit.relocatedPlacement (Gate.HadamardLayer.layout n)
          (context base noQuantum n count).quantumLayout (positions base noQuantum n count half)
          (dimensions base noQuantum n count half)).splitBasis basis).1 =
        selectedBasis base noQuantum n count half basis := by
    funext index
    apply Fin.ext
    change (((UnitaryCircuit.relocatedPlacement (Gate.HadamardLayer.layout n)
      (context base noQuantum n count).quantumLayout (positions base noQuantum n count half)
      (dimensions base noQuantum n count half)).splitBasis basis).1 index).val =
        (basis (positions base noQuantum n count half index)).val
    rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value]
    rfl
  rw [readBasis row, readBasis column]
  rfl

/-- The actual ordered Z writes, applied to one incoming complete store and basis. -/
def writtenStore (half : Fin 2) (store : Store (context base noQuantum n count))
    (basis : (context base noQuantum n count).register.Index) :
    Store (context base noQuantum n count) :=
  Circuit.writeMeasurementPath (allowAllocation := allowAllocation)
    (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := .empty)
    (readouts base noQuantum n count half) store
    (Circuit.measurementBasisPath (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts base noQuantum n count half) basis)

/-- The real written outcome clears exactly the selected half, leaving the other half intact. -/
lemma correction_written_column (half : Fin 2)
    (store : Store (context base noQuantum n count))
    (row column : (context base noQuantum n count).register.Index) :
    (correction (oracles := oracles) base noQuantum n count half
      ((writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half store column).read
          (QubitReadouts.input (cells base noQuantum n count)))).matrix environment.quantum row
            column =
      (if selectedBasis base noQuantum n count half row =
        (Gate.HadamardLayer.layout n).zeroLabel then 1 else 0) *
      (if spectators base noQuantum n count half row =
        spectators base noQuantum n count half column then 1 else 0) := by
  rw [correction_entry]
  have mask : QubitReadouts.mask
      ((writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half store column).read
          (QubitReadouts.input (cells base noQuantum n count))) =
      fun index => decide ((selectedBasis base noQuantum n count half column index).val = 1) := by
    funext index
    exact QubitReadouts.written_mask (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (services := .empty)
      (positions base noQuantum n count half) (qubits base noQuantum n count half)
      (cells base noQuantum n count) (cells_distinct base noQuantum n count) store column index
  rw [mask, ZReset.BankParallel.Correction.layer_reset_column]

private lemma basisPath_equal {ctx : RuntimeCtx .quantum}
    (items : List (ZReadout ctx)) (row column : ctx.register.Index)
    (agree : Circuit.measurementLabelsAgree items row column) :
    Circuit.measurementBasisPath (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty) items row =
    Circuit.measurementBasisPath (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty) items column := by
  induction items with
  | nil => rfl
  | cons head tail ih => exact Prod.ext agree.1 (ih agree.2)

/-- Coherent labels surviving the measurement have precisely the same actual write path. -/
lemma writtenStore_equal (half : Fin 2) (store : Store (context base noQuantum n count))
    (row column : (context base noQuantum n count).register.Index)
    (agree : Circuit.measurementLabelsAgree (readouts base noQuantum n count half) row column) :
    writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half store row =
    writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half store column := by
  unfold writtenStore
  rw [basisPath_equal (allowAllocation := allowAllocation) (oracles := oracles) _ row column agree]

/-- Grouping history retains each complete incoming store block under an arbitrary weight. -/
lemma weighted_store_sum {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (weight : Store ctx → ℂ) (left right : (Register.prod ctx.register Reference).Index) :
    ExecutionState.weightedMatrixEntry state (fun entry => weight entry.1) left right =
      ∑ original : Store ctx, weight original *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          left right := by
  simp_rw [ExecutionState.filterClassical_matrix_weighted]
  unfold ExecutionState.weightedMatrixEntry
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  simp only [mul_ite, one_mul, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- A batch's exact full matrix, grouped by actual incoming and final stores. -/
lemma batch_store_entry (half : Fin 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (stored : Store (context base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((batch (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix (left, leftRef) (right, rightRef) =
      ∑ column : (context base noQuantum n count).register.Index,
        (∑ row : (context base noQuantum n count).register.Index,
          (correction (oracles := oracles) base noQuantum n count half
            (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
              environment.quantum left row *
          (if Circuit.measurementLabelsAgree (readouts base noQuantum n count half) row column
          then ∑ original : Store (context base noQuantum n count),
            if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
              base noQuantum n count half original row = stored then
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
                (row, leftRef) (column, rightRef) else 0
          else 0)) * star ((correction (oracles := oracles) base noQuantum n count half
            (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
              environment.quantum
              right column) := by
  rw [show batch (allowAllocation := allowAllocation) (oracles := oracles)
    base noQuantum n count half = Circuit.seq
      (Circuit.measurementSequence (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := BitWord.model) (classicalOracles := .empty)
        (readouts base noQuantum n count half))
      (.branch (QubitReadouts.input (cells base noQuantum n count))
        (fun value => .unitary (correction base noQuantum n count half value))) from rfl,
    Circuit.measuredSelectedUnitary_store_entry]
  apply Finset.sum_congr rfl
  intro column _
  apply congrArg (fun value : ℂ => value * star
    ((correction (oracles := oracles) base noQuantum n count half
      (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
        environment.quantum right column))
  apply Finset.sum_congr rfl
  intro row _
  apply congrArg (fun value : ℂ =>
    (correction (oracles := oracles) base noQuantum n count half
      (stored.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
        environment.quantum left row * value)
  by_cases agree : Circuit.measurementLabelsAgree (readouts base noQuantum n count half) row column
  · rw [if_pos agree, if_pos agree]
    refine (weighted_store_sum (ctx := context base noQuantum n count)
      (Reference := Reference) state
      (fun original => if writtenStore (allowAllocation := allowAllocation)
        (oracles := oracles) base noQuantum n count half original row = stored then 1 else 0)
      (row, leftRef) (column, rightRef)).trans ?_
    apply Finset.sum_congr rfl
    intro original _
    split_ifs <;> simp only [one_mul, zero_mul]
  · rw [if_neg agree, if_neg agree]

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
