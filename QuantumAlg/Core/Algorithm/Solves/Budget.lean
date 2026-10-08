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
theorem enlargeBudgets {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    {algorithm : Algorithm model pre post shape} {problem : Problem model pre post shape}
    (solves : Algorithm.Solves algorithm problem)
    (resources : ResourceBudget model) (depth : DepthBudget model)
    (events : problem.resources.events ≤ resources.events)
    (resident : problem.resources.resident ≤ resources.resident)
    (auxiliary : problem.resources.auxiliary ≤ resources.auxiliary)
    (duration : depth.duration = problem.depth.duration)
    (limit : problem.depth.limit ≤ depth.limit) :
    Algorithm.Solves algorithm { problem with resources := resources, depth := depth } where
  success := solves.success
  states := solves.states
  borrowed := solves.borrowed
  events := fun reference input valid initialized path supported =>
    (solves.events reference input valid initialized path supported).trans events
  resident := fun reference input valid initialized path supported =>
    (solves.resident reference input valid initialized path supported).trans resident
  auxiliary := fun reference input valid initialized path supported =>
    (solves.auxiliary reference input valid initialized path supported).trans auxiliary
  depth := by
    intro reference input valid initialized path supported
    change algorithm.run.code.depth depth.duration path ≤ depth.limit
    rw [duration]
    exact (solves.depth reference input valid initialized path supported).trans limit

end

end QuantumAlg.Algorithm.Solves
