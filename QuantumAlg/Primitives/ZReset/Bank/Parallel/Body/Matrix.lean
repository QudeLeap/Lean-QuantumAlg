/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Program
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Correction.Matrix
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Measurement.Readout

/-!
# Exact complete blocks of the parallel reset body

The selected X layer is determined by the cells written by the actual
measurement sequence. Its output is zero in every complete final-store
block, with each arbitrary reference entry equal to the corresponding
input diagonal fiber. No basis-state input or independent reference is
assumed, and no measurement outcomes are supplied separately from execution.
-/

namespace QuantumAlg.ZReset.BankParallel

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {allowAllocation : Bool} {ctx : RuntimeCtx .quantum} {width : Nat}
  {oracles : OracleModel} {operations : ClassicalOpModel} {services : ClassicalOracleModel}

variable {environment : (ExecutionModel.quantum AlgorithmGate.model
  oracles operations services).Environment}

private lemma labelsAgree_iff (readouts : List (ZReadout ctx))
    (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree readouts left right ↔
      ∀ item ∈ readouts, left item.wire = right item.wire := by
  induction readouts with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail ih => simp [Circuit.measurementLabelsAgree, ih]

/-- Measuring every physical bank position suppresses exactly unequal complete labels. -/
lemma readouts_labelsAgree (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree
      (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells)
      left right ↔ left = right := by
  rw [labelsAgree_iff]
  constructor
  · intro agree
    funext wire
    obtain ⟨index, rfl⟩ := positions.surjective wire
    exact agree _ (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro same
    subst right
    intro _ _
    rfl

/-- The store obtained from the body's actual measurement path on a complete basis label. -/
def writtenStore (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (store : Store ctx) (basis : ctx.register.Index) : Store ctx :=
  Circuit.writeMeasurementPath (allowAllocation := allowAllocation)
    (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := operations) (classicalOracles := services)
    (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells) store
    (Circuit.measurementBasisPath (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := operations) (classicalOracles := services)
      (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells) basis)

/-- The real written cells select the exact zero column on the original physical bank. -/
lemma correction_written_column (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    (store : Store ctx) (row column : ctx.register.Index) :
    (Correction.program ctx.quantumLayout qubits oracles
      (fun wire => QubitReadouts.mask
        ((writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          (operations := operations) (services := services)
          positions qubits cells store column).read (QubitReadouts.input cells))
        (positions.symm wire))).matrix environment.quantum row column =
      if row = ctx.quantumLayout.zeroLabel then 1 else 0 := by
  have written (wire : Fin ctx.systemCount) :
      QubitReadouts.mask
        ((writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          (operations := operations) (services := services)
          positions qubits cells store column).read (QubitReadouts.input cells))
        (positions.symm wire) = decide ((column wire).val = 1) := by
    refine (QubitReadouts.written_mask (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := operations) (services := services)
        positions (fun index => qubits (positions index)) cells distinct
        store column (positions.symm wire)).trans ?_
    exact congrArg (fun position => decide ((column position).val = 1))
      (positions.apply_symm_apply wire)
  simp_rw [written]
  exact Correction.program_reset_column ctx.quantumLayout qubits oracles row column

/-- Every complete final store retains precisely its actual measurement fiber and reference block.
-/
lemma body_store_entry (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (((body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).execute
        environment Reference state).filterClassical
          (fun entry => entry.1 = stored)).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index, ∑ original : Store ctx × (services.HiddenState × History),
          if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
            (operations := operations) (services := services)
            positions qubits cells original.1 basis = stored then
              (state.block original).matrix (basis, leftRef) (basis, rightRef)
          else 0
      else 0 := by
  let program := fun value => Correction.program ctx.quantumLayout qubits oracles
    (fun wire => QubitReadouts.mask value (positions.symm wire))
  have actual := Circuit.measuredSelectedUnitary_store_entry (environment := environment)
    (allowAllocation := allowAllocation)
    (operations := operations) (classicalOracles := services)
    (QubitReadouts.readouts positions (fun index => qubits (positions index)) cells)
    (QubitReadouts.input cells) program state stored left right leftRef rightRef
  refine actual.trans ?_
  simp only [readouts_labelsAgree, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [ExecutionState.weightedMatrixEntry, Finset.mul_sum, Finset.sum_mul]
  change (∑ basis : ctx.register.Index,
    ∑ original : Store ctx × (services.HiddenState × History),
      (program (stored.read (QubitReadouts.input cells))).matrix environment.quantum left basis *
        ((if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          (operations := operations) (services := services)
          positions qubits cells original.1 basis = stored then 1 else 0) *
            (state.block original).matrix (basis, leftRef) (basis, rightRef)) *
        star ((program (stored.read (QubitReadouts.input cells))).matrix
          environment.quantum right basis)) = _
  have term (basis : ctx.register.Index)
      (original : Store ctx × (services.HiddenState × History)) :
      (program (stored.read (QubitReadouts.input cells))).matrix environment.quantum left basis *
        ((if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          (operations := operations) (services := services)
          positions qubits cells original.1 basis = stored then 1 else 0) *
            (state.block original).matrix (basis, leftRef) (basis, rightRef)) *
        star ((program (stored.read (QubitReadouts.input cells))).matrix
          environment.quantum right basis) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
          (operations := operations) (services := services)
          positions qubits cells original.1 basis = stored then
            (state.block original).matrix (basis, leftRef) (basis, rightRef) else 0
      else 0 := by
    by_cases sameStore : writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        (operations := operations) (services := services)
        positions qubits cells original.1 basis = stored
    · have leftColumn := correction_written_column
        (environment := environment) (allowAllocation := allowAllocation)
        (oracles := oracles) (operations := operations) (services := services)
        positions qubits cells distinct original.1 left basis
      have rightColumn := correction_written_column
          (environment := environment) (allowAllocation := allowAllocation)
        (oracles := oracles) (operations := operations) (services := services)
        positions qubits cells distinct original.1 right basis
      rw [sameStore] at leftColumn rightColumn
      simp only [program, leftColumn, rightColumn, sameStore, if_true, one_mul]
      split_ifs <;> simp_all
    · simp only [sameStore, if_false, zero_mul, mul_zero, ite_self]
  simp_rw [term]
  split_ifs <;> simp

end

end QuantumAlg.ZReset.BankParallel
