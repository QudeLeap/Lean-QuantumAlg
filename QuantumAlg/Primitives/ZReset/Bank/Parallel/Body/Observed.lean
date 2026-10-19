/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Body.Matrix

/-!
# Complete reference blocks selected by an untouched store predicate

The measurement fiber equation is summed over complete final stores.
Any predicate preserved by the actual scalar writes therefore keeps its
entire input reference matrix. In particular, this applies to equality
of the complete original parent store after removing the fresh scratch.
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

/-- A predicate-selected full matrix is the sum of its complete stored-value blocks. -/
lemma filter_store_matrix_sum {History : Type} [Fintype History] {Reference : Register}
    (state : State ctx Reference History) (predicate : Store ctx → Prop)
    (left right : (Register.prod ctx.register Reference).Index) :
    (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal.matrix left right =
      ∑ stored : Store ctx, if predicate stored then
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix left right
      else 0 := by
  simp_rw [ExecutionState.filterClassical_matrix_weighted]
  unfold ExecutionState.weightedMatrixEntry
  have distribute (stored : Store ctx) :
      (if predicate stored then
        ∑ original : Store ctx × History,
          (if original.1 = stored then (1 : ℂ) else 0) *
            (state.block original).matrix left right
      else 0) =
      ∑ original : Store ctx × History,
        if original.1 = stored then
          (if predicate stored then (state.block original).matrix left right else 0)
        else 0 := by
    by_cases selected : predicate stored <;> simp [selected]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul]

/-- The actual writes preserve any predicate that each declared destination preserves. -/
lemma writtenStore_predicate (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2)) (predicate : Store ctx → Prop)
    (preserved : ∀ (item : ZReadout ctx),
      item ∈ QubitReadouts.readouts positions (fun index => qubits (positions index)) cells →
        ∀ store value, predicate (store.write item.output value) ↔ predicate store)
    (store : Store ctx) (basis : ctx.register.Index) :
    predicate (writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services)
      positions qubits cells store basis) ↔ predicate store := by
  have writes (readouts : List (ZReadout ctx))
      (preserve : ∀ item ∈ readouts, ∀ store value,
        predicate (store.write item.output value) ↔ predicate store)
      (store : Store ctx)
      (path : (Circuit.measurementSequence (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := operations) (classicalOracles := services) readouts).Path) :
      predicate (Circuit.writeMeasurementPath (allowAllocation := allowAllocation)
        (gates := AlgorithmGate.model) (oracles := oracles)
        (operations := operations) (classicalOracles := services) readouts store path) ↔
          predicate store := by
    induction readouts generalizing store with
    | nil => rfl
    | cons head tail ih =>
        exact (ih (fun item member => preserve item (.tail head member))
          (store.write head.output (.finite path.1)) path.2).trans
          (preserve head (.head tail) store (.finite path.1))
  exact writes _ preserved store _

/-- Every untouched store predicate retains its full reference matrix while the bank becomes zero.
-/
lemma body_observed_entry (positions : Fin width ≃ Fin ctx.systemCount)
    (qubits : ∀ wire, (ctx.quantumLayout.wire wire).dimension = 2)
    (cells : Fin width → CWriteRef ctx (.finite 2))
    (distinct : Function.Injective fun index => (cells index).key)
    (predicate : Store ctx → Prop)
    (preserved : ∀ store basis,
      predicate (writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        (operations := operations) (services := services)
        positions qubits cells store basis) ↔ predicate store)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (((body (allowAllocation := allowAllocation) (oracles := oracles)
      (operations := operations) (services := services) positions qubits cells).execute
        environment Reference state).filterClassical
          (fun entry => predicate entry.1)).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => predicate entry.1)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 := by
  rw [filter_store_matrix_sum]
  simp_rw [body_store_entry positions qubits cells distinct]
  by_cases zero : left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel
  · simp only [if_pos zero]
    have distribute (stored : Store ctx) :
        (if predicate stored then
          ∑ basis : ctx.register.Index,
            ∑ original : Store ctx × (services.HiddenState × History),
              if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
                (operations := operations) (services := services)
                positions qubits cells original.1 basis = stored then
                  (state.block original).matrix (basis, leftRef) (basis, rightRef)
              else 0
        else 0) =
        ∑ basis : ctx.register.Index,
          ∑ original : Store ctx × (services.HiddenState × History),
            if writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
              (operations := operations) (services := services)
              positions qubits cells original.1 basis = stored then
                if predicate stored then
                  (state.block original).matrix (basis, leftRef) (basis, rightRef) else 0
            else 0 := by
      by_cases selected : predicate stored <;> simp [selected]
    simp_rw [distribute]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro basis _
    rw [Finset.sum_comm, ExecutionState.filterClassical_matrix_weighted]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, preserved,
      ExecutionState.weightedMatrixEntry, ite_mul, one_mul, zero_mul]
  · simp only [if_neg zero, ite_self, Finset.sum_const_zero]

end

end QuantumAlg.ZReset.BankParallel
