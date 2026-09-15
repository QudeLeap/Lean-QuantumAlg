/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources

/-!
# Complete native resource accounting for an actual sampled Shor iteration

The original fixed proposal sampler contributes its real random draw and
expanded arithmetic. Actual result-cell retention then precedes the compiled
quantum member, phase readout and complete bank reset/reload. All quantum and
classical event coordinates remain those of the existing single interpreter.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

namespace NativeStorage

variable (ctx : RuntimeCtx .quantum) (N : Nat)

private theorem allocation_trace (path : (allocate ctx N).Path) :
    (allocate ctx N).eventTrace path = [] :=
  Execution.MeasurementCells.allocate_eventTrace (resultContext ctx N) 2 (phaseBits N) path.2

private theorem allocation_depth (path : (allocate ctx N).Path) :
    (allocate ctx N).depth (fun _ => 1) path = 0 := by
  change 0 + (Execution.MeasurementCells.allocate (resultContext ctx N) 2 (phaseBits N)).depth
    (fun _ => 1) path.2 = 0
  rw [Execution.MeasurementCells.allocate_depth]

/-- Actual result allocation retains the same full native round event bound. -/
theorem round_pool_le
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (round ctx N sameWires parameter).Path) :
    (round ctx N sameWires parameter).resourcePool path ≤ NativeRound.eventEnvelope N := by
  change ResourcePool.ofList ((allocate ctx N).eventTrace path.1 ++
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)).eventTrace path.2) ≤ _
  rw [allocation_trace, List.nil_append]
  exact NativeRound.code_pool_le N ((quantumWires ctx N).trans sameWires)
    (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N) path.2

/-- Real retention adds no fictitious serial operation to the full actual quantum round. -/
theorem round_unitDepth_le
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (path : (round ctx N sameWires parameter).Path) :
    (round ctx N sameWires parameter).depth (fun _ => 1) path ≤ NativeRound.depthBound N := by
  change (allocate ctx N).depth (fun _ => 1) path.1 +
    (NativeRound.code N ((quantumWires ctx N).trans sameWires)
      (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N)).depth (fun _ => 1) path.2 ≤ _
  rw [allocation_depth, Nat.zero_add]
  exact NativeRound.code_unitDepth_le N ((quantumWires ctx N).trans sameWires)
    (liftInput ctx N parameter) (cells ctx N) (resultRef ctx N) path.2

end NativeStorage

namespace NativeIteration

/-- Both the real fixed-proposal sampler and full quantum round contribute native coordinates. -/
def eventEnvelope (N : Nat) : ResourcePool .quantum :=
  Sampler.Retained.nativeEnvelope .quantum N + NativeRound.eventEnvelope N

/-- The actual sampled parameter precedes all quantum operations and full bank reuse work. -/
def depthBound (N : Nat) : Nat := 44 * modulusBits N + 161 + NativeRound.depthBound N

variable (ctx : RuntimeCtx .quantum) (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Every sampled native iteration fits the independent complete event allowance. -/
theorem code_pool_le (path : (code ctx N sameWires).Path) :
    (code ctx N sameWires).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList ((Sampler.Retained.circuit ctx N).eventTrace path.1 ++
    (NativeStorage.round (sampledContext ctx N) N ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef)).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (Sampler.Retained.samplerRetained_pool_le ctx N path.1)
    (NativeStorage.round_pool_le (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef) path.2)

/-- Sampling, actual quantum work and mandatory reset/reload all contribute serial duration. -/
theorem code_unitDepth_le (path : (code ctx N sameWires).Path) :
    (code ctx N sameWires).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add (Sampler.Retained.samplerRetained_unit_depth_le ctx N path.1)
    (NativeStorage.round_unitDepth_le (sampledContext ctx N) N
      ((sampled_quantumWires ctx N).trans sameWires)
      (.storage (Sampler.Retained.parameterRef ctx N).toCStorageRef) path.2)

end NativeIteration

end

end QuantumAlg.Factoring.ShorStyle.Canonical
