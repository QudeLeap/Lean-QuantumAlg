/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual resources of a stored-result single-wire reset

The selected path charges one Z measurement and one native cyclic shift,
including the shift by zero. The feed-forward dependency is sequential.
Every path visits the same complete context twice, so both native space
peaks equal the caller's existing space, including the result cell.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))

private instance resourceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- The actual selected path contains the measurement followed by its read-back gate. -/
theorem resetCircuit_eventTrace (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).eventTrace path =
      [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension,
        .gate (gateLabel (-path.2.1.toFin))] := rfl

/-- Both native events are charged even when the measured value is zero. -/
theorem resetCircuit_pool (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).resourcePool path =
      ResourcePool.ofList [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension,
        .gate (gateLabel (-path.2.1.toFin))] := rfl

/-- The gate depends on the preceding measurement under any native event duration. -/
theorem resetCircuit_depth (duration : Resource.Event .quantum → Nat)
    (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).depth duration path =
      duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        duration (.gate (gateLabel (-path.2.1.toFin))) := rfl

/-- Unit event durations give exactly two sequential operations. -/
theorem resetCircuit_unitDepth (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).depth (fun _ => 1) path = 2 := rfl

/-- Measurement and correction retain the same actual context. -/
theorem resetCircuit_visited (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).visitedContexts path = [ctx, ctx] := rfl

/-- The resident peak is precisely the complete existing context. -/
theorem resetCircuit_resident (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).peakResidentSpace path = ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

/-- The auxiliary peak is precisely the existing roles of the same live cells. -/
theorem resetCircuit_auxiliary (path : (resetCircuit wire output).Path) :
    (resetCircuit wire output).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

end

end QuantumAlg.QuditShift
