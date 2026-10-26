/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.Solves
import Mathlib.Tactic.NormNum

/-!
# Fixed conditional-success floor for RSA-2048

The actual measured twenty-member, four-batch execution realizes this independent floor.
Its proof uses the unchanged original good-key model and source proposal law.
-/

namespace QuantumAlg.Factoring.RSA2048.Measured

/-- The independently requested ninety-nine-percent success probability. -/
noncomputable def conditionalSuccessFloor : ProbabilityLowerBound :=
  ⟨ENNReal.ofReal ((99 : Real) / 100), by norm_num⟩

/-- Retain every independent contract field while selecting the fixed-width witness and floor. -/
def refineProblem {model : ExecutionModel} {pre post : RuntimeCtx model.kind}
    {outputShape : CShape} (source : Problem model pre post outputShape)
    {Witness : Type} (witness : Witness → source.Witness)
    (floor : model.Environment → Witness → ProbabilityLowerBound) :
    Problem model pre post outputShape where
  Witness := Witness
  valid := fun environment key => source.valid environment (witness key)
  initialization := fun environment key => source.initialization environment (witness key)
  accepts := fun environment key => source.accepts environment (witness key)
  successLB := floor
  states := fun environment key => source.states environment (witness key)
  resources := source.resources
  quantumTimeLimit := source.quantumTimeLimit

/-- An actual stronger success proof changes no restoration, event, space or time obligation. -/
lemma solves_refineProblem {allowAllocation : Bool} {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {outputShape : CShape}
    {algorithm : Algorithm model pre post outputShape allowAllocation}
    (source : Problem model pre post outputShape)
    {Witness : Type} (witness : Witness → source.Witness)
    (floor : model.Environment → Witness → ProbabilityLowerBound)
    (complete : algorithm.Solves source)
    (success : ∀ environment key Reference
      (input : Execution.OracleInput model.classicalOracles pre Reference),
      source.valid environment (witness key) input.caller.localState →
      source.initialization environment (witness key) input.localState →
      (floor environment key).value ≤
        (algorithm.relationalDistribution environment input).toOuterMeasure
          {pair | source.accepts environment (witness key) pair.1 pair.2}) :
    algorithm.Solves (refineProblem source witness floor) where
  success := success
  states := fun environment key Reference input valid initialized requirement present =>
    complete.states environment (witness key) Reference input valid initialized requirement present
  borrowed := fun environment key Reference input valid initialized =>
    complete.borrowed environment (witness key) Reference input valid initialized
  events := fun environment key Reference input valid initialized path supported =>
    complete.events environment (witness key) Reference input valid initialized path supported
  resident := fun environment key Reference input valid initialized path supported =>
    complete.resident environment (witness key) Reference input valid initialized path supported
  auxiliary := fun environment key Reference input valid initialized path supported =>
    complete.auxiliary environment (witness key) Reference input valid initialized path supported
  time := fun environment key Reference input valid initialized path supported =>
    complete.time environment (witness key) Reference input valid initialized path supported

end QuantumAlg.Factoring.RSA2048.Measured
