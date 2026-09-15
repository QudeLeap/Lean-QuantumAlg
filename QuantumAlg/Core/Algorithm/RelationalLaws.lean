/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability

/-!
# Relational probabilities of actual execution records

An equation for the masses of every actual execution block determines the
run's execution distribution. Its relational distribution then reads the
initial store retained by that same run and the result selected by its
complete Output. The argument works even when the initial and final quantum
registers differ: probability comparison needs only the block traces.

Deterministic endpoints discharge the block equation from their actual
interpreter equations. Their independent arithmetic, storage and borrowed
restoration obligations remain part of their own correctness proofs.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {pre post : RuntimeCtx kind} {outputShape : CShape}

/-- Exact actual block masses determine the execution distribution of a mapped record. -/
theorem executionDistribution_eq_map_of_block_mass
    (run : AlgorithmRun pre post outputShape) {Reference : Register}
    (input : Execution.Input pre Reference)
    (record : Execution.Store pre → run.Record)
    (blocks : ∀ value,
      ((run.execute Reference input.state).block value).mass =
        ((input.state.mapClassical record).block value).mass) :
    run.executionDistribution input = (input.state.toPMF input.normalized).map record := by
  apply PMF.ext
  intro value
  change ENNReal.ofReal (((run.execute Reference input.state).block value).mass) = _
  rw [blocks value]
  exact congrArg (fun distribution : PMF run.Record => distribution value)
    (ExecutionState.toPMF_mapClassical input.state input.normalized record)

/-- Read the actual run's retained initial store and complete Output after mapping its records. -/
theorem relationalDistribution_eq_map_of_block_mass
    (run : AlgorithmRun pre post outputShape) {Reference : Register}
    (input : Execution.Input pre Reference)
    (record : Execution.Store pre → run.Record)
    (blocks : ∀ value,
      ((run.execute Reference input.state).block value).mass =
        ((input.state.mapClassical record).block value).mass) :
    run.relationalDistribution input =
      (input.state.toPMF input.normalized).map
        (fun store => ((record store).2.1, run.result (record store))) := by
  change (run.executionDistribution input).map
    (fun value => (value.2.1, run.result value)) = _
  exact (congrArg
    (fun distribution : PMF run.Record =>
      distribution.map (fun value => (value.2.1, run.result value)))
    (executionDistribution_eq_map_of_block_mass run input record blocks)).trans
      (PMF.map_comp _ _ _)

end

end QuantumAlg.AlgorithmRun
