/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Recursion
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Actual Fourier stage grouped by complete original storage

Only mathematical histories are summed. The real original store, all physical
matrix coordinates and the external reference remain in each branch. This
form composes directly with the successor theorem of the same native code.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum}

private lemma stored_matrix_sum_history {Reference : Register} {History : Type}
    [Fintype History] (state : State ctx Reference History) (stored : Store ctx) :
    (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ history : History, (state.block (stored, history)).matrix := by
  rw [← BasisSeeded.store_matrix]
  change (∑ entry : Store ctx × History,
    if entry.1 = stored then (state.block entry).matrix else 0) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single stored]
  · simp only [if_true]
  · intro other _ different
    simp only [if_neg different, Finset.sum_const_zero]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

/-- The literal native stage acts linearly on every complete original stored density. -/
lemma nativeStage_store_blocks_matrix {environment : (ExecutionModel.quantum AlgorithmGate.model
    .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((stageCode inverse head headQubit tail tailQubits result).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Fin (ctx.quantumLayout.wire head).dimension,
        if original.write result (.finite outcome) = stored then
          nativeStageKraus
            (environment := environment.quantum) inverse head headQubit tail tailQubits Reference
            outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeStageKraus
                (environment := environment.quantum) inverse head headQubit tail tailQubits
                Reference outcome).conjTranspose
        else 0 := by
  have native := nativeStage_store_matrix
    (environment := environment) inverse head headQubit tail tailQubits result state stored
  change _ = _ at native
  refine native.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : original.write result (.finite outcome) = stored
  · simp only [if_pos written]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, ← stored_matrix_sum_history]
  · simp only [if_neg written, Finset.sum_const_zero]

/-- Actual finite measurement values use the same two source outcome bits. -/
lemma nativeStage_store_binary_blocks_matrix {environment : (ExecutionModel.quantum
    AlgorithmGate.model .empty).Environment} (inverse : Bool) {n : Nat}
    (head : Fin ctx.systemCount)
    (headQubit : (ctx.quantumLayout.wire head).dimension = 2)
    (tail : Fin n ↪ Fin ctx.systemCount)
    (tailQubits : ∀ i, (ctx.quantumLayout.wire (tail i)).dimension = 2)
    (result : CWriteRef ctx (.finite (ctx.quantumLayout.wire head).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((stageCode inverse head headQubit tail tailQubits result).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ bit : Fin 2,
        let outcome := Fin.cast
          (congrArg (fun size : ℕ+ => (size : Nat)) headQubit).symm bit
        if original.write result (.finite outcome) = stored then
          nativeStageKraus
            (environment := environment.quantum) inverse head headQubit tail tailQubits Reference
            outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeStageKraus
                (environment := environment.quantum) inverse head headQubit tail tailQubits
                Reference outcome).conjTranspose
        else 0 := by
  rw [nativeStage_store_blocks_matrix]
  apply Finset.sum_congr rfl
  intro original _
  exact (Equiv.sum_comp
    (finCongr (congrArg (fun size : ℕ+ => (size : Nat)) headQubit)).symm _).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
