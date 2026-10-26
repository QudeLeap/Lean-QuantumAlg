/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Blocks
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Instrument
import all QuantumAlg.Core.Execution.Store.History

/-!
# Complete instrument of the actual recycled Fourier readout

The branch word is formed from the literal corrected native stages in the
same structural recursion as the executed program. Original stored blocks,
all actual result writes and arbitrary service, History and Reference remain
in the exact finite sum. The original generic stored-conjugation composition
law is reused; no alternate executor or semantic certificate is supplied.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The actual finite measured value obtained from its dimension-certified source bit. -/
def headOutcome (ports : Ports ctx totalBits (active + 1)) (bit : Fin 2) :
    Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension :=
  Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (ports.qubits 0)).symm bit

/-- The literal MZ writes, with every original cell and overwrite collision retained. -/
def outcomeStore : (count : Nat) → Ports ctx totalBits count → Store ctx → Bits count → Store ctx
  | 0, _, original, _ => original
  | count + 1, ports, original, (head, tail) =>
      outcomeStore count ports.tail
        (original.write (ports.measuredOutput 0) (.finite (headOutcome ports head))) tail

/-- Only actual corrected stage matrices occur in the complete branch product. -/
def outcomeKraus (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    (count : Nat) → Ports ctx totalBits count → Bits count →
      HilbertOperator (ctx.register.prod Reference)
  | 0, _, _ => 1
  | count + 1, ports, (head, tail) =>
      outcomeKraus environment Reference count ports.tail tail *
        nativeStageKraus ports environment Reference (headOutcome ports head)

/-- Actual corrected stages act linearly on every complete original stored block. -/
lemma window_stage_store_blocks_matrix (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((stage ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension,
        if original.write (ports.measuredOutput 0) (.finite outcome) = stored then
          nativeStageKraus ports environment.quantum Reference outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeStageKraus ports environment.quantum Reference outcome).conjTranspose
        else 0 := by
  refine (window_stage_store_matrix ports environment state stored).trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : original.write (ports.measuredOutput 0) (.finite outcome) = stored
  · simp only [if_pos written]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum,
      ← _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.stored_matrix_sum_history]
  · simp only [if_neg written, Finset.sum_const_zero]

lemma window_stage_store_binary_blocks_matrix (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((stage ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ bit : Fin 2,
        if original.write (ports.measuredOutput 0) (.finite (headOutcome ports bit)) = stored then
          nativeStageKraus ports environment.quantum Reference (headOutcome ports bit) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (nativeStageKraus ports environment.quantum Reference
                (headOutcome ports bit)).conjTranspose
        else 0 := by
  rw [window_stage_store_blocks_matrix]
  apply Finset.sum_congr rfl
  intro original _
  exact (Equiv.sum_comp
    (finCongr (congrArg (fun size : ℕ+ => (size : Nat)) (ports.qubits 0))).symm _).symm

lemma window_readout_zero_store (ports : Ports ctx totalBits 0)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((readout 0 ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  rw [readout, Circuit.execute_id]
  calc
    _ = (ExecutionState.filterClassical
        (state.mapHistory (fun record => (record.1, (record.2, ()))))
        (fun entry => entry.1 = stored)).quantumMarginal := by
      apply congrArg (fun result : State ctx Reference
        (services.HiddenState × (History × Unit)) =>
          (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal)
      exact ExecutionState.executionState_mapClassical_congr state rfl
    _ = _ := State.mapHistory_store_marginal _ _ _

/-- The same executed bank recursion has its full original-Store corrected-Kraus instrument. -/
lemma window_readout_instrument_store_matrix
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (count : Nat) (ports : Ports ctx totalBits count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((readout count ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits count,
        if outcomeStore count ports original outcome = stored then
          outcomeKraus environment.quantum Reference count ports outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (outcomeKraus environment.quantum Reference count ports outcome).conjTranspose
        else 0 := by
  induction count generalizing History with
  | zero =>
      rw [window_readout_zero_store]
      change _ = ∑ original : Store ctx, ∑ _ : Unit,
        if original = stored then
          (1 : HilbertOperator (ctx.register.prod Reference)) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (1 : HilbertOperator (ctx.register.prod Reference)).conjTranspose
        else 0
      simp only [Fintype.sum_unique, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ count ih =>
      rw [window_readout_succ_store]
      refine (ih ports.tail ((stage ports).execute environment Reference state)).trans ?_
      have stageBlocks := fun original =>
        window_stage_store_binary_blocks_matrix ports environment state original
      have regrouped := congrArg
        (fun density : Store ctx → HilbertOperator (ctx.register.prod Reference) =>
          ∑ intermediate : Store ctx, ∑ outcome : Bits count,
            if outcomeStore count ports.tail intermediate outcome = stored then
              outcomeKraus environment.quantum Reference count ports.tail outcome *
                density intermediate *
                  (outcomeKraus environment.quantum Reference count ports.tail
                    outcome).conjTranspose
            else 0) (funext stageBlocks)
      refine regrouped.trans ?_
      refine (_root_.QuantumAlg.QuantumFourierTransform.Semiclassical.storedConjugation_compose
        (S := Store ctx) (First := Fin 2) (Second := Bits count)
        (R := ctx.register.prod Reference)
        (fun (bit : Fin 2) (original : Store ctx) => original.write (ports.measuredOutput 0)
          (.finite (headOutcome ports bit)))
        (fun (outcome : Bits count) (original : Store ctx) =>
          outcomeStore count ports.tail original outcome)
        (fun bit : Fin 2 =>
          nativeStageKraus ports environment.quantum Reference (headOutcome ports bit))
        (fun outcome : Bits count =>
          outcomeKraus environment.quantum Reference count ports.tail outcome)
        (fun original : Store ctx =>
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix)
        stored).trans ?_
      change _ = ∑ original : Store ctx, ∑ outcome : Fin 2 × Bits count,
        if outcomeStore (count + 1) ports original outcome = stored then
          outcomeKraus environment.quantum Reference (count + 1) ports outcome *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (outcomeKraus environment.quantum Reference (count + 1) ports outcome).conjTranspose
        else 0
      simp only [Fintype.sum_prod_type, outcomeKraus, outcomeStore]
      rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
