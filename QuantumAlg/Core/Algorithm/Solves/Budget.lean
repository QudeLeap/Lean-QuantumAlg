/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Algorithm.Solves

/-!
# Transport to independently proved resource ceilings

Budget comparison is separate from the dependent execution tree. The same
algorithm, input and service domains, acceptance, state promises and borrowed
restoration are retained. Only independently justified upper bounds change.
-/

namespace QuantumAlg.Algorithm.Solves

noncomputable section

/-- Increasing independently supplied ceilings preserves every same-run obligation. -/
lemma enlargeBudgets {allowAllocation : Bool} {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {algorithm : Algorithm model pre post shape allowAllocation}
    {problem : Problem model pre post shape}
    (solves : Algorithm.Solves algorithm problem)
    (resources : ResourceBudget model) (quantumTimeLimit : Nat)
    (events : problem.resources.events ≤ resources.events)
    (resident : problem.resources.resident ≤ resources.resident)
    (auxiliary : problem.resources.auxiliary ≤ resources.auxiliary)
    (limit : problem.quantumTimeLimit ≤ quantumTimeLimit) :
    Algorithm.Solves algorithm
      { problem with resources := resources, quantumTimeLimit := quantumTimeLimit } where
  success := solves.success
  states := solves.states
  borrowed := solves.borrowed
  events := fun environment witness reference input valid initialized path supported =>
    (solves.events environment witness
      reference input valid initialized path supported).trans events
  resident := fun environment witness reference input valid initialized path supported =>
    (solves.resident environment witness
      reference input valid initialized path supported).trans resident
  auxiliary := fun environment witness reference input valid initialized path supported =>
    (solves.auxiliary environment witness
      reference input valid initialized path supported).trans auxiliary
  time := fun environment witness reference input valid initialized path supported =>
    (solves.time environment witness
      reference input valid initialized path supported).trans limit

end

end QuantumAlg.Algorithm.Solves
