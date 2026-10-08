/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.State
import all QuantumAlg.Components.Classical.GF2.Native.Resources
import all QuantumAlg.Components.Classical.GF2.Native.Space
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Space

/-!
# Actual resources of the original seven-cell recovery workspace

The original seven shapes are allocated once around the entire recovery.
Its original scopes preserve the same path events and serial durations.
Live-space bounds add all seven true cell encodings, the existing additional
scratch allowance, and every original caller-context entry.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

noncomputable section

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- All seven real lexical scopes retain the original complete native event allowance. -/
theorem gf2WithState_pool_le (path : (withState input output).Path) :
    (withState input output).resourcePool path ≤ intoEnvelope model rowCount width := by
  apply ClassicalWorkspace.withCellsFrom_pool_le (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    (intoEnvelope model rowCount width) ?_ path
  intro inner cells _distinct transport _separated current
  exact gf2Into_pool_le (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output) current

/-- Actual initialization and release retain all original arbitrary event durations. -/
theorem gf2WithState_depth_le (duration : Resource.Event model → Nat)
    (path : (withState input output).Path) :
    (withState input output).depth duration path ≤ intoDepthLimit rowCount width duration := by
  apply ClassicalWorkspace.withCellsFrom_depth_le (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    duration (intoDepthLimit rowCount width duration) ?_ path
  intro inner cells _distinct transport _separated current
  exact gf2Into_depth_le (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output) duration current

/-- The actual lexical scopes preserve the exact same-path serial event-duration equation. -/
theorem gf2WithState_duration_eventTrace (duration : Resource.Event model → Nat)
    (path : (withState input output).Path) :
    (withState input output).depth duration path =
      (((withState input output).eventTrace path).map duration).sum := by
  have equation := ClassicalWorkspace.withCellsFrom_property (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    (fun _ code => ∀ selected : code.Path,
      code.depth duration selected = ((code.eventTrace selected).map duration).sum)
    (fun _ _ _ _ _ available => available)
    (fun {inner} cells _distinct transport _separated current =>
      gf2Into_duration_eventTrace (transport.liftInput input)
        cells.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
        cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
        (transport.liftWrite output) duration current)
  exact equation path

/-- Every actual instruction remains charged after the original seven cells are released. -/
theorem gf2WithState_eventCount_le (path : (withState input output).Path) :
    ((withState input output).eventTrace path).length ≤
      intoDepthLimit (model := model) rowCount width (fun _ => 1) := by
  have bound := gf2WithState_depth_le input output (fun _ => 1) path
  rw [gf2WithState_duration_eventTrace] at bound
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_one] using bound

/-- All seven real cells and the active body scratch count toward the full resident peak. -/
theorem gf2WithState_resident_le (path : (withState input output).Path) :
    (withState input output).peakResidentSpace path ≤
      ((stateShapes rowCount width).map SpacePool.ofShape).sum +
        intoScratchSpace model rowCount width + ctx.residentSpace := by
  apply ClassicalWorkspace.withCellsFrom_resident_le (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    (intoScratchSpace model rowCount width) ?_ path
  intro inner cells _distinct transport _separated current
  exact gf2Into_resident_le (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output) current

/-- All seven live workspace cells are charged once with the full caller auxiliary context. -/
theorem gf2WithState_auxiliary_le (path : (withState input output).Path) :
    (withState input output).peakAuxiliarySpace path ≤
      ((stateShapes rowCount width).map SpacePool.ofShape).sum +
        intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
  apply ClassicalWorkspace.withCellsFrom_auxiliary_le (Transport.id ctx)
    (stateShapes rowCount width)
    (fun cells _ transport _ => stateBody input output cells transport)
    (intoScratchSpace model rowCount width) ?_ path
  intro inner cells _distinct transport _separated current
  exact gf2Into_auxiliary_le (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
    cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
    (transport.liftWrite output) current

end

end QuantumAlg.ClassicalRoutines.GF2.Native
