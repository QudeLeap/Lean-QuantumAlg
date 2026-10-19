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

variable {allowAllocation : Bool}

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
  {outputShape : CShape}

/-- Exact actual block masses determine the execution distribution of a mapped record. -/
lemma executionDistribution_eq_map_of_block_mass
    (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (record : Execution.Store pre × model.HiddenState → run.Record)
    (blocks : ∀ value,
      ((run.execute environment Reference input.state).block value).mass =
        ((input.state.mapClassical record).block value).mass) :
    run.executionDistribution environment input =
      (input.state.toPMF input.normalized).map record := by
  apply PMF.ext
  intro value
  change ENNReal.ofReal (((run.execute environment Reference input.state).block value).mass) = _
  rw [blocks value]
  exact congrArg (fun distribution : PMF run.Record => distribution value)
    (ExecutionState.toPMF_mapClassical input.state input.normalized record)

/-- Read the actual run's retained initial store and complete Output after mapping its records. -/
lemma relationalDistribution_eq_map_of_block_mass
    (run : AlgorithmRun model pre post outputShape allowAllocation)
    (environment : model.Environment) {Reference : Register}
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (record : Execution.Store pre × model.HiddenState → run.Record)
    (blocks : ∀ value,
      ((run.execute environment Reference input.state).block value).mass =
        ((input.state.mapClassical record).block value).mass) :
    run.relationalDistribution environment input =
      (input.state.toPMF input.normalized).map
        (fun store => ((record store).2.2.1, run.result (record store))) := by
  change (run.executionDistribution environment input).map
    (fun value => (value.2.2.1, run.result value)) = _
  exact (congrArg
    (fun distribution : PMF run.Record =>
      distribution.map (fun value => (value.2.2.1, run.result value)))
    (executionDistribution_eq_map_of_block_mass run environment input record blocks)).trans
      (PMF.map_comp _ _ _)

end

end QuantumAlg.AlgorithmRun
