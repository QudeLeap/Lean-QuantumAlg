/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Path
import all QuantumAlg.Core.Execution.Trace.Boundary

/-!
# Actual finite reset-to-basis resources

Every wire contributes its Z measurement and one complete supplied correction
to the target. Both portions keep their sequential dependency.
Internal parallelism remains inside the corresponding circuit depth. Empty
circuits contribute no fictional shift event. Every stage retains the complete
original context, including result cells and all auxiliary roles.
-/

namespace QuantumAlg.QuditShift

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

private instance sequenceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- The stage records measurement and one direct correction in their actual order. -/
theorem resetWireToBasis_eventTrace (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire realizations output value).Path) :
    (resetWireToBasis wire realizations output value).eventTrace path =
      Circuit.zEvent (ctx.quantumLayout.wire wire).dimension ::
        (realizations (value - path.2.1.toFin)).circuit.eventTrace := rfl

/-- Every actual one-wire reset path contains its physical Z measurement. -/
theorem resetWireToBasis_measured (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire realizations output value).Path) :
    Resource.Event.measurement (model := .quantum gates oracles)
      (ctx.quantumLayout.wire wire).dimension ∈
      (resetWireToBasis wire realizations output value).eventTrace path := by
  simp [resetWireToBasis_eventTrace, Circuit.zEvent]

/-- Native counts come from these same complete actual traces. -/
theorem resetWireToBasis_pool (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire realizations output value).Path) :
    (resetWireToBasis wire realizations output value).resourcePool path =
      ResourcePool.ofList (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension ::
        (realizations (value - path.2.1.toFin)).circuit.eventTrace) := rfl

/-- Sequential depth preserves the actual dependencies inside each supplied circuit. -/
theorem resetWireToBasis_duration (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (path : (resetWireToBasis wire realizations output value).Path) :
    (resetWireToBasis wire realizations output value).depth duration path =
      duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        (realizations (value - path.2.1.toFin)).circuit.evaluatedEventDepth duration := rfl

/-- Measurement and correction retain exactly the original resident context. -/
theorem resetWireToBasis_resident (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire realizations output value).Path) :
    (resetWireToBasis wire realizations output value).peakResidentSpace path =
      ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace 0) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

/-- The same stage retains every original auxiliary role. -/
theorem resetWireToBasis_auxiliary (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis wire realizations output value).Path) :
    (resetWireToBasis wire realizations output value).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace 0) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

variable (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)
variable (count : Nat) (wires : Fin count → Fin ctx.systemCount)
  (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (label : ctx.quantumLayout.Basis)

/-- Every nonempty actual reset sequence measures at least its first selected wire. -/
theorem resetToBasisOn_measured (positive : 0 < count)
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := .quantum gates oracles) dimension ∈
      (resetToBasisOn implementations count wires outputs label).eventTrace path := by
  let first : Fin count := ⟨0, positive⟩
  let body : Fin count → Circuit (.quantum gates oracles) ctx ctx := fun index =>
    resetWireToBasis (wires index) (implementations (wires index))
      (outputs (wires index)) (label (wires index))
  change (Circuit.forRange count body).Path at path
  let firstPath := Circuit.forRangeComponentPath count body path first
  refine ⟨(ctx.quantumLayout.wire (wires first)).dimension, ?_⟩
  change Resource.Event.measurement (model := .quantum gates oracles) _ ∈
    (Circuit.forRange count body).eventTrace path
  rw [Circuit.forRange_eventTrace_eq]
  exact List.mem_flatten.mpr ⟨(body first).eventTrace firstPath,
    List.mem_ofFn.mpr ⟨first, rfl⟩,
    resetWireToBasis_measured (wires first) (implementations (wires first))
      (outputs (wires first)) (label (wires first)) firstPath⟩

/-- Resetting a nonempty physical layout includes an actual measurement on every path. -/
theorem resetToBasis_measured (positive : 0 < ctx.systemCount)
    (path : (resetToBasis implementations outputs label).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := .quantum gates oracles) dimension ∈
      (resetToBasis implementations outputs label).eventTrace path :=
  resetToBasisOn_measured implementations ctx.systemCount id outputs label positive path

/-- The exact total includes each stage's measurement and actual correction expansion. -/
theorem resetToBasisOn_eventCount
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    ((resetToBasisOn implementations count wires outputs label).eventTrace path).length =
      ∑ index, ((resetWireToBasis (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index))).eventTrace
          (Circuit.forRangeComponentPath count _ path index)).length :=
  Circuit.forRange_eventCount_eq_sum count _ path

/-- Actual stage depths add without resetting at measurements or flattening parallel bodies. -/
theorem resetToBasisOn_duration (duration : Resource.Event (.quantum gates oracles) → Nat)
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    (resetToBasisOn implementations count wires outputs label).depth duration path =
      ∑ index, (resetWireToBasis (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index))).depth duration
          (Circuit.forRangeComponentPath count _ path index) :=
  Circuit.forRange_depth_eq_sum count _ duration path

/-- Unit durations still measure the complete actual dependency tree of each stage. -/
theorem resetToBasisOn_unitDepth
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    (resetToBasisOn implementations count wires outputs label).depth (fun _ => 1) path =
      ∑ index, (resetWireToBasis (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index))).depth (fun _ => 1)
          (Circuit.forRangeComponentPath count _ path index) :=
  resetToBasisOn_duration implementations count wires outputs label (fun _ => 1) path

/-- An arbitrary finite reset order keeps the exact original resident peak. -/
theorem resetToBasisOn_resident
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    (resetToBasisOn implementations count wires outputs label).peakResidentSpace path =
      ctx.residentSpace := by
  apply le_antisymm
  · exact Circuit.forRange_resident_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_resident (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index)) path).le) path
  · exact Circuit.input_residentSpace_le_peak _ path

/-- An arbitrary finite reset order keeps every original auxiliary role. -/
theorem resetToBasisOn_auxiliary
    (path : (resetToBasisOn implementations count wires outputs label).Path) :
    (resetToBasisOn implementations count wires outputs label).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  apply le_antisymm
  · exact Circuit.forRange_auxiliary_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_auxiliary (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index)) path).le) path
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- The full physical register counts the actual expansions for every wire. -/
theorem resetToBasis_eventCount (path : (resetToBasis implementations outputs label).Path) :
    ((resetToBasis implementations outputs label).eventTrace path).length =
      ∑ wire, ((resetWireToBasis wire (implementations wire) (outputs wire) (label wire)).eventTrace
        (Circuit.forRangeComponentPath ctx.systemCount _ path wire)).length :=
  resetToBasisOn_eventCount implementations ctx.systemCount id outputs label path

/-- The complete direct basis preparation has the original resident peak. -/
theorem resetToBasis_resident (path : (resetToBasis implementations outputs label).Path) :
    (resetToBasis implementations outputs label).peakResidentSpace path = ctx.residentSpace :=
  resetToBasisOn_resident implementations ctx.systemCount id outputs label path

/-- The complete direct basis preparation has the original auxiliary peak. -/
theorem resetToBasis_auxiliary (path : (resetToBasis implementations outputs label).Path) :
    (resetToBasis implementations outputs label).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  resetToBasisOn_auxiliary implementations ctx.systemCount id outputs label path

end

end QuantumAlg.QuditShift
