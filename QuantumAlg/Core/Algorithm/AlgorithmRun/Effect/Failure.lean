/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.AlgorithmRun.Effect
import all QuantumAlg.Util.PMF

/-!
# Relational success from an actual retained failure event

An output relation that agrees on every supported execution record with a
stored Boolean flag has probability exactly one minus the physical effect
weight of the flag's false branch. The original input store remains in the
relation; no independence or replacement output distribution is assumed.
-/

namespace QuantumAlg.AlgorithmRun

noncomputable section

open Execution

variable {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
  {outputShape : CShape}

/-- A supported-record identification turns the complete run's relational
success into the complement of its actual failed-record effect weight. -/
theorem relational_success_eq_one_sub_failure_effectWeight
    (run : AlgorithmRun model pre post outputShape)
    {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference)
    (accepts : Store pre × outputShape.Value → Prop)
    (flag : run.Record → Bool)
    (agrees : ∀ record ∈ (run.executionDistribution input).support,
      accepts (record.2.2.1, run.result record) ↔ flag record = true) :
    (run.relationalDistribution input).toOuterMeasure {pair | accepts pair} =
      1 - ENNReal.ofReal ((run.execute Reference input.state).effectWeight
        (fun record => if flag record = false then
          Effect.one (post.register.prod Reference)
        else Effect.zero (post.register.prod Reference))) := by
  let distribution := run.executionDistribution input
  have eventEq :
      distribution.toOuterMeasure
          {record | accepts (record.2.2.1, run.result record)} =
        distribution.toOuterMeasure {record | flag record = true} := by
    apply distribution.toOuterMeasure_apply_eq_of_inter_support_eq
    ext record
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact and_congr_left (fun supported => agrees record supported)
  have failureEq :
      distribution.toOuterMeasure {record | flag record = false} =
        ENNReal.ofReal ((run.execute Reference input.state).effectWeight
          (fun record => if flag record = false then
            Effect.one (post.register.prod Reference)
          else Effect.zero (post.register.prod Reference))) := by
    calc
      distribution.toOuterMeasure {record | flag record = false} =
          (distribution.map flag).toOuterMeasure ({false} : Set Bool) := by
        rw [PMF.toOuterMeasure_map_apply]
        rfl
      _ = distribution.map flag false := PMF.toOuterMeasure_apply_singleton _ _
      _ = _ := run.executionDistribution_map_eq_effectWeight input flag false
  calc
    (run.relationalDistribution input).toOuterMeasure {pair | accepts pair} =
        distribution.toOuterMeasure
          {record | accepts (record.2.2.1, run.result record)} := by
      simp only [AlgorithmRun.relationalDistribution, PMF.toOuterMeasure_map_apply]
      rfl
    _ = distribution.toOuterMeasure {record | flag record = true} := eventEq
    _ = 1 - distribution.toOuterMeasure {record | flag record = false} := by
      have complement : {record | ¬ flag record = true} =
          {record | flag record = false} := by
        ext record
        cases h : flag record <;> simp [h]
      rw [PMF.eventProbability_eq_one_sub_complement, complement]
    _ = _ := congrArg (1 - ·) failureEq

end

end QuantumAlg.AlgorithmRun
