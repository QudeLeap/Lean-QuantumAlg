/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual finite reset-to-basis resources

Every wire contributes its Z measurement, read-back correction, and prescribed
basis shift. Both shifts are counted even when their amount is zero. The
existing sequence preserves their serial dependencies under arbitrary native
durations. Every stage keeps the complete original context, so neither space
peak grows, also for an empty physical layout or aliased result cells.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {ctx : RuntimeCtx .quantum}

private instance sequenceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- The actual stage charges all three native operations, in their execution order. -/
theorem resetWireToBasis_eventTrace (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire output value).Path) :
    (resetWireToBasis wire output value).eventTrace path =
      [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension,
        .gate (gateLabel (-path.1.2.1.toFin)), .gate (gateLabel value)] := rfl

/-- The same three actual events determine the stage's complete native pool. -/
theorem resetWireToBasis_pool (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire output value).Path) :
    (resetWireToBasis wire output value).resourcePool path =
      ResourcePool.ofList [Circuit.zEvent (ctx.quantumLayout.wire wire).dimension,
        .gate (gateLabel (-path.1.2.1.toFin)), .gate (gateLabel value)] := rfl

/-- Each stage's dependency depth is the sum of its actual native event durations. -/
theorem resetWireToBasis_duration (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (duration : Resource.Event .quantum → Nat)
    (path : (resetWireToBasis wire output value).Path) :
    (resetWireToBasis wire output value).depth duration path =
      (((resetWireToBasis wire output value).eventTrace path).map duration).sum := by
  change (duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
    duration (.gate (gateLabel (-path.1.2.1.toFin)))) + duration (.gate (gateLabel value)) =
      duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        (duration (.gate (gateLabel (-path.1.2.1.toFin))) +
          (duration (.gate (gateLabel value)) + 0))
  omega

/-- One reset-and-seed stage retains exactly the original resident context. -/
theorem resetWireToBasis_resident (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire output value).Path) :
    (resetWireToBasis wire output value).peakResidentSpace path = ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace (SpacePool.max ctx.residentSpace 0)) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

/-- The stage also retains exactly the original auxiliary roles. -/
theorem resetWireToBasis_auxiliary (wire : Fin ctx.systemCount)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire output value).Path) :
    (resetWireToBasis wire output value).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace (SpacePool.max ctx.auxiliarySpace 0)) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

variable (count : Nat) (wires : Fin count → Fin ctx.systemCount)
  (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (label : ctx.quantumLayout.Basis)

/-- All three actual events are counted for every indexed stage. -/
theorem resetToBasisOn_eventCount (path : (resetToBasisOn count wires outputs label).Path) :
    ((resetToBasisOn count wires outputs label).eventTrace path).length = 3 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (_ ++ (resetToBasisOn count (fun index => wires index.succ) outputs label).eventTrace
        path.2).length = _
      exact List.length_append.trans
        ((congrArg (fun length => 3 + length)
          (ih (fun index => wires index.succ) path.2)).trans (by omega))

/-- Actual dependency depth adds the actual chronological event durations for the whole sequence. -/
theorem resetToBasisOn_duration (duration : Resource.Event .quantum → Nat)
    (path : (resetToBasisOn count wires outputs label).Path) :
    (resetToBasisOn count wires outputs label).depth duration path =
      (((resetToBasisOn count wires outputs label).eventTrace path).map duration).sum :=
  Circuit.forRange_duration_eventTrace count _ duration
    (fun index => resetWireToBasis_duration (wires index) (outputs (wires index))
      (label (wires index)) duration) path

/-- Unit durations charge exactly three serial operations per selected wire. -/
theorem resetToBasisOn_unitDepth (path : (resetToBasisOn count wires outputs label).Path) :
    (resetToBasisOn count wires outputs label).depth (fun _ => 1) path = 3 * count := by
  rw [resetToBasisOn_duration]
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] using
    resetToBasisOn_eventCount count wires outputs label path

/-- An arbitrary finite reset order keeps the exact original resident peak. -/
theorem resetToBasisOn_resident (path : (resetToBasisOn count wires outputs label).Path) :
    (resetToBasisOn count wires outputs label).peakResidentSpace path = ctx.residentSpace := by
  apply le_antisymm
  · exact Circuit.forRange_resident_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_resident (wires index) (outputs (wires index))
        (label (wires index)) path).le) path
  · exact Circuit.input_residentSpace_le_peak _ path

/-- An arbitrary finite reset order keeps the exact original auxiliary peak. -/
theorem resetToBasisOn_auxiliary (path : (resetToBasisOn count wires outputs label).Path) :
    (resetToBasisOn count wires outputs label).peakAuxiliarySpace path = ctx.auxiliarySpace := by
  apply le_antisymm
  · exact Circuit.forRange_auxiliary_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_auxiliary (wires index) (outputs (wires index))
        (label (wires index)) path).le) path
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- The complete physical register incurs three real operations per existing system. -/
theorem resetToBasis_eventCount (path : (resetToBasis outputs label).Path) :
    ((resetToBasis outputs label).eventTrace path).length = 3 * ctx.systemCount :=
  resetToBasisOn_eventCount ctx.systemCount id outputs label path

/-- The complete reset-and-seed execution has the original resident peak. -/
theorem resetToBasis_resident (path : (resetToBasis outputs label).Path) :
    (resetToBasis outputs label).peakResidentSpace path = ctx.residentSpace :=
  resetToBasisOn_resident ctx.systemCount id outputs label path

/-- The complete reset-and-seed execution has the original auxiliary peak. -/
theorem resetToBasis_auxiliary (path : (resetToBasis outputs label).Path) :
    (resetToBasis outputs label).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  resetToBasisOn_auxiliary ctx.systemCount id outputs label path

end

end QuantumAlg.QuditShift
