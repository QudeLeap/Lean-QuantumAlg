/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Protocol
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Cycle.Protocol
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
import all QuantumAlg.Core.Algorithm.ExecutionState.Map

/-!
# Actual next-input admission for the binary reusable bank

The initialization predicate observes the local joint caller/service state.
Tracing out an arbitrary external reference commutes with summing complete
classical blocks. The real reset therefore supplies the next protocol's zero
input without resetting hidden services or replacing any stored sample
[dW19, qcnotes.tex:5381-5420].
-/

namespace QuantumAlg.FiniteCyclicDLP.Reusable.Cycle

noncomputable section

open Execution

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Local joint initialization and the actual full state's local marginal agree exactly. -/
public lemma reusableCycle_localState_quantumMarginal (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register}
    (input : OracleInput (model P).classicalOracles (context P count) Reference) :
    input.localState.quantumMarginal = input.state.quantumMarginal.marginalLeft := by
  apply DensityOperator.ext
  ext row column
  change (∑ value : Store (context P count) × (model P).HiddenState,
    (input.localState.block value).matrix) row column = _
  simp only [Matrix.sum_apply, OracleInput.oracleInput_localState_block,
    DensityOperator.marginalLeft_matrix]
  change (∑ value : Store (context P count) × (model P).HiddenState,
    ∑ reference : Reference.Index,
      (input.state.block value).matrix (row, reference) (column, reference)) =
    ∑ reference : Reference.Index,
      (∑ value : Store (context P count) × (model P).HiddenState,
        (input.state.block value).matrix) (row, reference) (column, reference)
  simp only [Matrix.sum_apply]
  exact Finset.sum_comm

/-- The independent local initialization promise applies to the actual arbitrary reference input. -/
public lemma input_pure (P : KnownOrderProblem G) (count : Nat)
    {Reference : Register}
    (input : OracleInput (model P).classicalOracles (context P count) Reference)
    (admitted : initialized P count input.localState) :
    (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
      (context P count).quantumLayout.zeroLabel)).Holds
        input.state.quantumMarginal.marginalLeft := by
  unfold initialized at admitted
  rwa [reusableCycle_localState_quantumMarginal] at admitted

/-- Every real terminal reset admits the next sample on the very same stored output state. -/
public lemma round_nextInput_initialized (P : KnownOrderProblem G) {count : Nat}
    (slot : Fin count) (expansion : OrderExpansion P.order)
    {Reference : Register}
    (input : OracleInput (model P).classicalOracles (context P count) Reference) :
    initialized P count ((round P slot expansion).nextInput
      (sourceEnvironment P) input).localState := by
  classical
  unfold initialized
  rw [reusableCycle_localState_quantumMarginal]
  change (StatePromise.pure (NormalizedVector.ket (R := (context P count).register)
    (context P count).quantumLayout.zeroLabel)).Holds
      (((round P slot expansion).execute (sourceEnvironment P) Reference
        (input.state.mapClassical (fun entry => (entry.1, (entry.2, ()))))).mapClassical
          (fun record => (record.1, record.2.1))).quantumMarginal.marginalLeft
  rw [ExecutionState.mapClassical_quantumMarginal]
  exact round_pure P slot expansion _

end

end QuantumAlg.FiniteCyclicDLP.Reusable.Cycle
