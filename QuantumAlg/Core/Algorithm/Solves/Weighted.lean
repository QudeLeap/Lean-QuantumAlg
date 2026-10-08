/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-! # Weighted event consequences of a solved algorithm problem -/

namespace QuantumAlg

/-- A supported path inherits any nonnegative weighted event ceiling proved
for the independent problem's event budget. -/
public theorem weightedCount_le_of_solves
    {model : ExecutionModel} {pre post : RuntimeCtx model.kind} {outputShape : CShape}
    (algorithm : Algorithm model pre post outputShape)
    (problem : Problem model pre post outputShape)
    (weight : Resource.Event model → Nat) (limit : Nat)
    (solves : algorithm.Solves problem)
    (budget : ResourcePool.weightedCount weight problem.resources.events ≤ limit)
    (Reference : Register)
    (input : Execution.OracleInput model.classicalOracles pre Reference)
    (valid : problem.valid input.caller.localState)
    (initialized : problem.initialization input.localState)
    (path : algorithm.run.code.Path)
    (supported : algorithm.run.Supports Reference input.state path) :
    ResourcePool.weightedCount weight (algorithm.run.code.resourcePool path) ≤ limit := by
  exact (ResourcePool.weightedCount_mono weight
    (solves.events Reference input valid initialized path supported)).trans budget

end QuantumAlg
