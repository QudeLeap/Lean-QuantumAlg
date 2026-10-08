/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank
import all QuantumAlg.Primitives.ZReset.Sequence.Frame
import all QuantumAlg.Primitives.ZReset.Sequence.OperationModel
import all QuantumAlg.Core.Execution.Classical.Pushforward
import all QuantumAlg.Core.Execution.State.History

/-!
# Actual preserved-read probabilities across complete bank reset

Every structural read avoiding the one real reset destination keeps its
probability, under any classical operation grant. Decoding or grouping those
read values also keeps their probabilities. No incoming independence or
positive-probability assumption is required.
-/

namespace QuantumAlg.ZReset.Bank

noncomputable section

open Execution

attribute [local instance] Classical.decEq Classical.propDecidable

private theorem observed_mass {C D : Type} [Fintype C] [Fintype D] [DecidableEq D] {R : Register}
    (state : ExecutionState C R) (read : C → D) (value : D) :
    ((state.mapClassical read).block value).mass =
      ∑ entry : C, if read entry = value then (state.block entry).mass else 0 := by
  change (∑ entry : C, if read entry = value then (state.block entry).matrix else 0).trace.re = _
  rw [Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro entry _
  by_cases selected : read entry = value <;>
    simp only [selected, if_true, if_false, Matrix.trace_zero, Complex.zero_re,
      DensityOperator.mass]

private theorem observed_mass_filter {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
    {R : Register}
    (state : ExecutionState C R) (read : C → D) (value : D) :
    ((state.mapClassical read).block value).mass =
      (state.filterClassical (fun entry => read entry = value)).mass := by
  rw [observed_mass, ExecutionState.filterClassical_mass]

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}

/-- The real complete reset leaves each untouched read fiber at its original mass. -/
theorem zResetBank_read_mass
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : scratch.key ∉ observed.storageKeys) (value : shape.Value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations).HiddenState × History)) :
    ((((code (oracles := oracles) qubits scratch operations).execute Reference state).mapClassical
      (fun entry => entry.1.read observed)).block value).mass =
      ((state.mapClassical (fun entry => entry.1.read observed)).block value).mass := by
  have erased := congrArg
    (fun output => ((output.mapClassical (fun entry => entry.1.read observed)).block value).mass)
    (ZReset.sequence_execute_operationModel (implementations (oracles := oracles) qubits)
      (readouts qubits scratch) operations state)
  simp only [State.mapHistory, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def] at erased
  change ((((ZReset.sequence (implementations (oracles := oracles) qubits)
    (readouts qubits scratch) operations).execute Reference state).mapClassical
      (fun entry => entry.1.read observed)).block value).mass = _
  rw [erased, observed_mass_filter]
  rw [ZReset.zReset_sequence_filter_read _ _ observed
    (fun item present => by
      rw [zResetBank_readouts_key qubits scratch item present]
      exact separate) value Reference state, Circuit.execute_mass]
  exact (observed_mass_filter state (fun entry => entry.1.read observed) value).symm

/-- Grouping actual preserved read values keeps their original complete fiber probabilities. -/
theorem zResetBank_decoded_read_mass
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (scratch : CWriteRef ctx (.finite 2)) (operations : ClassicalOpModel)
    {shape : CShape} (observed : CInputRef ctx shape)
    (separate : scratch.key ∉ observed.storageKeys)
    {D : Type} [Fintype D] [DecidableEq D] (decode : shape.Value → D) (value : D)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles operations).HiddenState × History)) :
    ((((code (oracles := oracles) qubits scratch operations).execute Reference state).mapClassical
      (fun entry => decode (entry.1.read observed))).block value).mass =
      ((state.mapClassical (fun entry => decode (entry.1.read observed))).block value).mass := by
  have left := ExecutionState.executionState_mapClassical_comp
    ((code (oracles := oracles) qubits scratch operations).execute Reference state)
    (fun entry => entry.1.read observed) decode
  have right := ExecutionState.executionState_mapClassical_comp state
    (fun entry => entry.1.read observed) decode
  simp only [Function.comp_def] at left right
  rw [← left, ← right, observed_mass, observed_mass]
  apply Finset.sum_congr rfl
  intro result _
  rw [zResetBank_read_mass qubits scratch operations observed separate result state]

end

end QuantumAlg.ZReset.Bank
