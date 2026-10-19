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
lemma resetWireToBasis_eventTrace {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).eventTrace path =
      Circuit.zEvent (ctx.quantumLayout.wire wire).dimension ::
        (realizations (value - path.2.1.toFin)).circuit.eventTrace := rfl

/-- Every actual one-wire reset path contains its physical Z measurement. -/
lemma resetWireToBasis_measured {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    Resource.Event.measurement (model := .quantum gates oracles)
      (ctx.quantumLayout.wire wire).dimension ∈
      (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
          value).eventTrace path := by
  simp [resetWireToBasis_eventTrace (allowAllocation := allowAllocation), Circuit.zEvent]

/-- Native counts come from these same complete actual traces. -/
lemma resetWireToBasis_pool {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).resourcePool path =
      ResourcePool.ofList (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension ::
        (realizations (value - path.2.1.toFin)).circuit.eventTrace) := rfl

/-- Sequential depth preserves the actual dependencies inside each supplied circuit. -/
lemma resetWireToBasis_duration {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output value).depth
        duration path =
      duration (Circuit.zEvent (ctx.quantumLayout.wire wire).dimension) +
        (realizations (value - path.2.1.toFin)).circuit.evaluatedEventDepth duration := rfl

/-- Measurement and correction retain exactly the original resident context. -/
lemma resetWireToBasis_resident {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).peakResidentSpace path =
      ctx.residentSpace := by
  change SpacePool.max ctx.residentSpace
    (SpacePool.max ctx.residentSpace 0) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

/-- The same stage retains every original auxiliary role. -/
lemma resetWireToBasis_auxiliary {allowAllocation : Bool} (wire : Fin ctx.systemCount)
    (realizations : Realizations gates oracles ctx.quantumLayout wire)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (value : Fin (ctx.quantumLayout.wire wire).dimension)
    (path : (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).Path) :
    (resetWireToBasis (allowAllocation := allowAllocation) wire realizations output
        value).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  change SpacePool.max ctx.auxiliarySpace
    (SpacePool.max ctx.auxiliarySpace 0) = _
  simp only [SpacePool.max_zero, SpacePool.max_self]

variable (implementations : ∀ wire, Realizations gates oracles ctx.quantumLayout wire)
variable (count : Nat) (wires : Fin count → Fin ctx.systemCount)
  (outputs : ∀ wire, CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (label : ctx.quantumLayout.Basis)

/-- Every nonempty actual reset sequence measures at least its first selected wire. -/
lemma resetToBasisOn_measured {allowAllocation : Bool} (positive : 0 < count)
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := .quantum gates oracles) dimension ∈
      (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
          label).eventTrace path := by
  let first : Fin count := ⟨0, positive⟩
  let body : Fin count → Circuit (.quantum gates oracles) ctx ctx allowAllocation := fun index =>
    resetWireToBasis (allowAllocation := allowAllocation) (wires index)
      (implementations (wires index)) (outputs (wires index)) (label (wires index))
  change (Circuit.forRange count body).Path at path
  let firstPath := Circuit.forRangeComponentPath count body path first
  refine ⟨(ctx.quantumLayout.wire (wires first)).dimension, ?_⟩
  change Resource.Event.measurement (model := .quantum gates oracles) _ ∈
    (Circuit.forRange count body).eventTrace path
  rw [Circuit.forRange_eventTrace_eq]
  exact List.mem_flatten.mpr ⟨(body first).eventTrace firstPath,
    List.mem_ofFn.mpr ⟨first, rfl⟩,
    resetWireToBasis_measured (allowAllocation := allowAllocation) (wires first)
      (implementations (wires first)) (outputs (wires first)) (label (wires first)) firstPath⟩

/-- Resetting a nonempty physical layout includes an actual measurement on every path. -/
lemma resetToBasis_measured {allowAllocation : Bool} (positive : 0 < ctx.systemCount)
    (path : (resetToBasis (allowAllocation := allowAllocation) implementations outputs label).Path)
        :
    ∃ dimension : ℕ+, Resource.Event.measurement (model := .quantum gates oracles) dimension ∈
      (resetToBasis (allowAllocation := allowAllocation) implementations outputs label).eventTrace
          path :=
  resetToBasisOn_measured (allowAllocation := allowAllocation) implementations ctx.systemCount id
      outputs label positive path

/-- The exact total includes each stage's measurement and actual correction expansion. -/
lemma resetToBasisOn_eventCount {allowAllocation : Bool}
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    ((resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).eventTrace path).length =
      ∑ index, ((resetWireToBasis (allowAllocation := allowAllocation) (wires index)
          (implementations (wires index))
        (outputs (wires index)) (label (wires index))).eventTrace
          (Circuit.forRangeComponentPath count _ path index)).length :=
  Circuit.forRange_eventCount_eq_sum count _ path

/-- Actual stage depths add without resetting at measurements or flattening parallel bodies. -/
lemma resetToBasisOn_duration {allowAllocation : Bool}
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).depth duration path =
      ∑ index, (resetWireToBasis (allowAllocation := allowAllocation) (wires index)
        (implementations (wires index)) (outputs (wires index))
        (label (wires index))).depth duration
          (Circuit.forRangeComponentPath count _ path index) :=
  Circuit.forRange_depth_eq_sum count _ duration path

/-- Unit durations still measure the complete actual dependency tree of each stage. -/
lemma resetToBasisOn_unitDepth {allowAllocation : Bool}
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).depth (fun _ => 1) path =
      ∑ index, (resetWireToBasis (allowAllocation := allowAllocation) (wires index)
        (implementations (wires index)) (outputs (wires index))
        (label (wires index))).depth (fun _ => 1)
          (Circuit.forRangeComponentPath count _ path index) :=
  resetToBasisOn_duration (allowAllocation := allowAllocation) implementations count wires outputs
      label (fun _ => 1) path

/-- An arbitrary finite reset order keeps the exact original resident peak. -/
lemma resetToBasisOn_resident {allowAllocation : Bool}
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).peakResidentSpace path =
      ctx.residentSpace := by
  apply le_antisymm
  · exact Circuit.forRange_resident_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_resident (allowAllocation := allowAllocation)
        (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index)) path).le) path
  · exact Circuit.input_residentSpace_le_peak _ path

/-- An arbitrary finite reset order keeps every original auxiliary role. -/
lemma resetToBasisOn_auxiliary {allowAllocation : Bool}
    (path : (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).Path) :
    (resetToBasisOn (allowAllocation := allowAllocation) implementations count wires outputs
        label).peakAuxiliarySpace path =
      ctx.auxiliarySpace := by
  apply le_antisymm
  · exact Circuit.forRange_auxiliary_le count _ _ le_rfl
      (fun index path => (resetWireToBasis_auxiliary (allowAllocation := allowAllocation)
        (wires index) (implementations (wires index))
        (outputs (wires index)) (label (wires index)) path).le) path
  · exact Circuit.input_auxiliarySpace_le_peak _ path

/-- The full physical register counts the actual expansions for every wire. -/
lemma resetToBasis_eventCount {allowAllocation : Bool}
    (path : (resetToBasis (allowAllocation := allowAllocation)
      implementations outputs label).Path) :
    ((resetToBasis (allowAllocation := allowAllocation) implementations outputs label).eventTrace
        path).length =
      ∑ wire, ((resetWireToBasis (allowAllocation := allowAllocation) wire (implementations wire)
          (outputs wire) (label wire)).eventTrace
        (Circuit.forRangeComponentPath ctx.systemCount _ path wire)).length :=
  resetToBasisOn_eventCount (allowAllocation := allowAllocation) implementations ctx.systemCount id
      outputs label path

/-- The complete direct basis preparation has the original resident peak. -/
lemma resetToBasis_resident {allowAllocation : Bool}
    (path : (resetToBasis (allowAllocation := allowAllocation)
      implementations outputs label).Path) :
    (resetToBasis (allowAllocation := allowAllocation) implementations outputs
        label).peakResidentSpace path = ctx.residentSpace :=
  resetToBasisOn_resident (allowAllocation := allowAllocation) implementations ctx.systemCount id
      outputs label path

/-- The complete direct basis preparation has the original auxiliary peak. -/
lemma resetToBasis_auxiliary {allowAllocation : Bool}
    (path : (resetToBasis (allowAllocation := allowAllocation)
      implementations outputs label).Path) :
    (resetToBasis (allowAllocation := allowAllocation) implementations outputs
        label).peakAuxiliarySpace path = ctx.auxiliarySpace :=
  resetToBasisOn_auxiliary (allowAllocation := allowAllocation) implementations ctx.systemCount id
      outputs label path

end

end QuantumAlg.QuditShift
