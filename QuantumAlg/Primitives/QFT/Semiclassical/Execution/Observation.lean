/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Refined.Lowering
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.SourceRows
import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.MarginalLaws

/-!
# Actual stored observations of the separately counted Fourier program

The complete final-store formula is pushed through an arbitrary read of those
same stores. Every original store and every measured bit tuple is included,
including zero-mass branches and colliding writes. The unconditional formula
then sums the actual original density blocks, retaining every reference entry.
No state-independence or prescribed output distribution is assumed.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma sum_stored_fibers {S O V A : Type}
    [Fintype S] [Fintype O] [AddCommMonoid A]
    (write : S → O → S) (read : S → V) (value : V) (branch : S → O → A) :
    (∑ stored : S, if read stored = value then
      ∑ original : S, ∑ outcome : O,
        if write original outcome = stored then branch original outcome else 0
      else 0) =
      ∑ original : S, ∑ outcome : O,
        if read (write original outcome) = value then branch original outcome else 0 := by
  calc
    _ = ∑ stored : S, ∑ original : S, ∑ outcome : O,
        if write original outcome = stored then
          if read stored = value then branch original outcome else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro stored _
      by_cases selected : read stored = value
      · simp only [selected, if_true]
      · simp only [selected, if_false, ite_self, Finset.sum_const_zero]
    _ = ∑ original : S, ∑ outcome : O, ∑ stored : S,
        if write original outcome = stored then
          if read stored = value then branch original outcome else 0 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro original _
      exact Finset.sum_comm
    _ = _ := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {ctx : RuntimeCtx .quantum}

/-- Fine native execution has the source instrument at every complete actual final store. -/
lemma refinedCode_source_store_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((Refined.code inverse n wires qubits outputs).execute environment) Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits n,
        if outcomeStore wires qubits outputs original outcome = stored then
          sourceOutcomeKraus inverse Reference n wires qubits outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (sourceOutcomeKraus inverse Reference n wires qubits outcome).conjTranspose
        else 0 := by
  rw [Refined.code_lowering_store_matrix]
  exact code_source_instrument_store_matrix inverse n wires qubits outputs state stored

/-- Reading real stored values aggregates exactly the actual final-store fibers. -/
lemma refinedCode_source_read_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    {Value : Type} [Fintype Value] (read : Store ctx → Value) (value : Value) :
    ((((Refined.code inverse n wires qubits outputs).execute environment)
      Reference state).mapClassical
      (fun entry => read entry.1) |>.block value).matrix =
      ∑ original : Store ctx, ∑ outcome : Bits n,
        if read (outcomeStore wires qubits outputs original outcome) = value then
          sourceOutcomeKraus inverse Reference n wires qubits outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (sourceOutcomeKraus inverse Reference n wires qubits outcome).conjTranspose
        else 0 := by
  rw [BasisSeeded.readout_matrix]
  simp_rw [refinedCode_source_store_matrix]
  exact sum_stored_fibers (outcomeStore wires qubits outputs) read value _

/-- Forgetting all results retains the full dephased quantum-reference density at its input mass. -/
lemma refinedCode_source_quantumMarginal_matrix {environment : (ExecutionModel.quantum
    SemiclassicalFourierGate.model .empty).Environment} (inverse : Bool) (n : Nat)
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ i, (ctx.quantumLayout.wire (wires i)).dimension = 2)
    (outputs : ∀ i, CWriteRef ctx (.finite (ctx.quantumLayout.wire (wires i)).dimension))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (((Refined.code inverse n wires qubits outputs).execute environment)
      Reference state).quantumMarginal.matrix =
      ∑ outcome : Bits n,
        sourceOutcomeKraus inverse Reference n wires qubits outcome *
          state.quantumMarginal.matrix *
            (sourceOutcomeKraus inverse Reference n wires qubits outcome).conjTranspose := by
  let : DecidableEq Unit := Classical.decEq Unit
  have grouped := refinedCode_source_read_matrix
    (environment := environment) inverse n wires qubits outputs state
    (fun _ => ()) ()
  rw [ExecutionState.executionState_mapClassical_const_block] at grouped
  simp only [if_true] at grouped
  rw [grouped, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, sum_store_matrices]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
