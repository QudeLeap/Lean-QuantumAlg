/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Native
public import QuantumAlg.Core.Execution.Classical.Query
public import QuantumAlg.Core.Execution.Random.Kernel
public import QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Store
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Actual state updates for declared classical operations and queries

Each step reads its placed operands, samples the declaration-owned transition
and writes the actual result. Quantum blocks retain their full context and
external reference, weighted by the actual transition probability.

A query carries its hidden state alongside the mathematical history, outside
the caller-addressable Store. Its output contains the next hidden state, so
composition passes that state to the next query without initialization. Native
operations can preserve such a state as part of their untouched history.
-/

namespace QuantumAlg.Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History : Type} [Fintype History]

/-- Read actual native operands, sample the selected token and store its result. -/
public def nativeStep {model : ClassicalOpModel}
    (application : model.Application ctx) (state : State ctx Reference History) :
    State ctx Reference (History × (model.outputShape application.token).Value) :=
  (kernelChoice state fun entry =>
    model.evaluate application.token (entry.1.read application.input)).mapClassical fun entry =>
      (entry.1.1.write application.output entry.2, (entry.1.2, entry.2))

/-- A declared native operation preserves the complete input probability mass. -/
public theorem nativeStep_mass {model : ClassicalOpModel}
    (application : model.Application ctx) (state : State ctx Reference History) :
    (nativeStep application state).mass = state.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (kernelChoice_mass _ _)

/-- Native sampling and classical storage updates preserve the full quantum marginal. -/
public theorem nativeStep_quantumMarginal {model : ClassicalOpModel}
    (application : model.Application ctx) (state : State ctx Reference History) :
    (nativeStep application state).quantumMarginal = state.quantumMarginal :=
  (ExecutionState.mapClassical_quantumMarginal _ _).trans (kernelChoice_quantumMarginal _ _)

open scoped Classical in
/-- Every output block sums precisely the weighted inputs that write that actual record. -/
public theorem nativeStep_block_matrix {model : ClassicalOpModel}
    (application : model.Application ctx) (state : State ctx Reference History)
    (result : Store ctx × (History × (model.outputShape application.token).Value)) :
    ((nativeStep application state).block result).matrix =
      ∑ entry : Store ctx × History, ∑ outcome,
        if (entry.1.write application.output outcome, (entry.2, outcome)) = result then
          (model.evaluate application.token (entry.1.read application.input) outcome).toReal •
            (state.block entry).matrix
        else 0 := by
  change (∑ entry : (Store ctx × History) × (model.outputShape application.token).Value,
    if (entry.1.1.write application.output entry.2, (entry.1.2, entry.2)) = result then
      ((kernelChoice state fun value =>
        model.evaluate application.token (value.1.read application.input)).block entry).matrix
    else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [kernelChoice_block_matrix]

/-- Sample the joint next-state/result transition using the current persistent state. -/
public def queryStep {model : ClassicalOracleModel}
    (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × History)) :
    State ctx Reference
      (model.HiddenState × (History × (model.outputShape application.query).Value)) :=
  (kernelChoice state fun entry =>
    model.transition application.query entry.2.1 (entry.1.read application.input)).mapClassical
      fun entry => (entry.1.1.write application.output entry.2.2,
        (entry.2.1, (entry.1.2.2, entry.2.2)))

/-- Stateful query execution retains the total probability of all correlated inputs. -/
public theorem queryStep_mass {model : ClassicalOracleModel}
    (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × History)) :
    (queryStep application state).mass = state.mass :=
  (ExecutionState.mapClassical_mass _ _).trans (kernelChoice_mass _ _)

/-- A classical query preserves every quantum and reference marginal entry. -/
public theorem queryStep_quantumMarginal {model : ClassicalOracleModel}
    (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × History)) :
    (queryStep application state).quantumMarginal = state.quantumMarginal :=
  (ExecutionState.mapClassical_quantumMarginal _ _).trans (kernelChoice_quantumMarginal _ _)

open scoped Classical in
/-- Query blocks retain actual input, old state, next state and visible-result correlations. -/
public theorem queryStep_block_matrix {model : ClassicalOracleModel}
    (application : model.Application ctx)
    (state : State ctx Reference (model.HiddenState × History))
    (result : Store ctx ×
      (model.HiddenState × (History × (model.outputShape application.query).Value))) :
    ((queryStep application state).block result).matrix =
      ∑ entry : Store ctx × (model.HiddenState × History),
        ∑ outcome : model.HiddenState × (model.outputShape application.query).Value,
          if (entry.1.write application.output outcome.2,
              (outcome.1, (entry.2.2, outcome.2))) = result then
            (model.transition application.query entry.2.1
              (entry.1.read application.input) outcome).toReal • (state.block entry).matrix
          else 0 := by
  change (∑ entry : (Store ctx × (model.HiddenState × History)) ×
      (model.HiddenState × (model.outputShape application.query).Value),
    if (entry.1.1.write application.output entry.2.2,
        (entry.2.1, (entry.1.2.2, entry.2.2))) = result then
      ((kernelChoice state fun value =>
        model.transition application.query value.2.1
          (value.1.read application.input)).block entry).matrix
    else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [kernelChoice_block_matrix]

end

end QuantumAlg.Execution
