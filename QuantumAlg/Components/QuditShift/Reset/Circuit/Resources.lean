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

The selected path charges one Z measurement followed by every actual native
operation of its supplied correction. The feed-forward dependency is sequential.
Every path visits the same complete context twice, so both native space
peaks equal the caller's existing space, including the result cell.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {services : ClassicalOracleModel}

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
variable {ctx : RuntimeCtx .quantum} (wire : Fin ctx.systemCount)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (realizations : Realizations gates oracles ctx.quantumLayout wire)

private instance resourceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- The actual selected path contains the measurement followed by its read-back gate. -/
lemma resetCircuit_eventTrace {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).eventTrace path =
      Circuit.zEvent (ctx.quantumLayout.wire wire).dimension operations services ::
        (realizations (-path.2.1.toFin)).circuit.eventTrace operations services := rfl

/-- The resource pool counts the actual correction without declaring a native shift. -/
lemma resetCircuit_pool {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).resourcePool path =
      ResourcePool.ofList (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension operations
        services ::
        (realizations (-path.2.1.toFin)).circuit.eventTrace operations services) := rfl

/-- The dependency expression retains the selected correction's complete internal tree. -/
lemma resetCircuit_eventDepth {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).eventDepth path =
      .seq (.atom (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension operations services))
        ((realizations (-path.2.1.toFin)).circuit.eventDepth operations services) := rfl

/-- The gate depends on the preceding measurement under any native event duration. -/
lemma resetCircuit_depth {allowAllocation : Bool}
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat)
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).depth duration path =
      duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension operations services) +
        DepthExpr.depthEval duration
          ((realizations (-path.2.1.toFin)).circuit.eventDepth operations services) := rfl

/-- Unit depth includes the complete selected implementation after its measurement. -/
lemma resetCircuit_unitDepth {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).depth (fun _ => 1)
      path =
      1 + DepthExpr.depthEval (fun _ => 1)
        ((realizations (-path.2.1.toFin)).circuit.eventDepth operations services) := rfl

/-- Measurement and correction retain the same actual context. -/
lemma resetCircuit_visited {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).visitedContexts path
      = [ctx, ctx] := rfl

/-- The resident peak is precisely the complete existing context. -/
lemma resetCircuit_resident {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).peakResidentSpace
      path =
      ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

/-- The auxiliary peak is precisely the existing roles of the same live cells. -/
lemma resetCircuit_auxiliary {allowAllocation : Bool}
    (path : (resetCircuit (allowAllocation := allowAllocation) (services := services)
      wire output realizations operations).Path) :
    (resetCircuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).peakAuxiliarySpace
      path =
      ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0) = _
  rw [SpacePool.max_zero, SpacePool.max_self]

end

end QuantumAlg.QuditShift
