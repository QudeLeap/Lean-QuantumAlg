/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Qubit
public import Mathlib.Tactic.Linter.Style
import all QuantumAlg.Core.Base.Depth.Expr
import all QuantumAlg.Core.Base.State.Pure

/-!
# Typed terminal computational-basis measurement

A `QubitLayout n` injectively places the `n` logical qubits on physical
systems. A `TerminalZMeasure layout k` then injectively selects `k` logical
qubits from that layout. The order of the selection is the canonical output-bit
order. No selected outcome or probability is stored in the descriptor.

The API remains terminal-only: it does not expose state collapse, a
mid-circuit branch, feed-forward, or a classical-register model. Strict
accounting emits one descriptor-derived measurement event per selected qubit,
while all selected qubits form one parallel depth layer.
-/

section

namespace QuantumAlg

namespace QubitLayout

/-- A normalized qubit state whose physical placement realizes one typed layout. -/
structure State {qubitCount : Nat} (layout : QubitLayout qubitCount) where
  /-- Normalized state vector with physical placement metadata. -/
  state : PureState (Qubits qubitCount)
  /-- The state metadata realizes the layout used by circuits and measurements. -/
  system_idx_eq : state.system_idx = layout.systemIdx
namespace State

/-- Metadata-free normalized value used by mathematical state consumers. -/
def normalized {qubitCount : Nat} {layout : QubitLayout qubitCount}
    (state : QubitLayout.State layout) : NormalizedVector (Qubits qubitCount) :=
  state.state.state

@[simp]
theorem normalized_coe {qubitCount : Nat} {layout : QubitLayout qubitCount}
    (state : QubitLayout.State layout) :
    ((state.normalized : NormalizedVector (Qubits qubitCount)) :
      HilbertVector (Qubits qubitCount)) = state.state := rfl

end State

end QubitLayout

/-- A terminal Z measurement selecting `measuredQubits` logical qubits from a
typed full-register layout. -/
public structure TerminalZMeasure {totalQubits : Nat}
    (layout : QubitLayout totalQubits) (measuredQubits : Nat) where
  /-- Logical qubits, in canonical output-bit order. -/
  logical_idx : Fin measuredQubits → Fin totalQubits
  /-- A logical qubit cannot be selected twice. -/
  logical_idx_injective : Function.Injective logical_idx

attribute [nolint defsWithUnderscore] TerminalZMeasure.logical_idx

/-- Select an injectively indexed subset of logical qubits for terminal Z
measurement. -/
def zMeasureAt {totalQubits measuredQubits : Nat}
    (layout : QubitLayout totalQubits)
    (logical_idx : Fin measuredQubits → Fin totalQubits)
    (logical_idx_injective : Function.Injective logical_idx) :
    TerminalZMeasure layout measuredQubits where
  logical_idx := logical_idx
  logical_idx_injective := logical_idx_injective

/-- Measure every logical qubit in logical-index order. -/
def zMeasure {qubitCount : Nat} (layout : QubitLayout qubitCount) :
    TerminalZMeasure layout qubitCount :=
  zMeasureAt layout id Function.injective_id

namespace TerminalZMeasure

/-- Fixed-length classical output of a typed terminal measurement. -/
public abbrev Outcome (measuredQubits : Nat) : Type :=
  Fin measuredQubits → Bool

/-- The base-layer logical selection derived from this measurement's own
position map and injectivity certificate. Accounting transitions consume this
same value rather than accepting an unrelated measured width. -/
public def selection {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    QubitSelection totalQubits measuredQubits :=
  QubitSelection.ofLogicalIdx measurement.logical_idx
    measurement.logical_idx_injective

@[simp] theorem selection_logical_idx {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    measurement.selection.logical_idx = measurement.logical_idx := rfl

/-- Physical systems measured, in the same order as the output bits. -/
def systemIdx {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) : List Nat :=
  List.ofFn fun index => layout.physical_idx (measurement.logical_idx index)

@[simp] theorem systemIdx_length {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    measurement.systemIdx.length = measuredQubits := by
  simp [systemIdx]

theorem systemIdx_nodup {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    measurement.systemIdx.Nodup := by
  apply List.nodup_ofFn.mpr
  exact layout.physical_idx_injective.comp measurement.logical_idx_injective

/-- A typed `k`-qubit result has exactly `2^k` possible bit vectors. -/
theorem outcome_card (measuredQubits : Nat) :
    Fintype.card (Outcome measuredQubits) = 2 ^ measuredQubits := by
  simp [Outcome]

/-- Each selected physical qubit is measured in its two-dimensional Z basis.

The descriptor retains the ordered logical placement. The accounting coordinate
records the actual system dimension shared by all native Z measurements.
-/
def eventLabel {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (_measurement : TerminalZMeasure layout measuredQubits) : ℕ+ := 2

variable (gates : GateModel) (oracles : OracleModel)
  (classical : ClassicalOpModel) (services : ClassicalOracleModel)

/-- One strict quantum event occurrence for a selected terminal measurement
qubit.  The occurrence has no caller-supplied label or multiplicity. -/
def event {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    Resource.Event (.quantum gates oracles classical services) :=
  .measurement measurement.eventLabel

/-- Ordered strict event occurrences for terminal measurement. -/
def eventTrace {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    List (Resource.Event (.quantum gates oracles classical services)) :=
  List.replicate measuredQubits (measurement.event gates oracles classical services)

/-- Strict event pool obtained by forgetting the order of the actual trace. -/
def eventCost {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    ResourcePool (.quantum gates oracles classical services) :=
  ResourcePool.ofList (measurement.eventTrace gates oracles classical services)

/-- All strict terminal-measurement events form one parallel depth layer. -/
def eventDepth {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    DepthExpr (Resource.Event (.quantum gates oracles classical services)) :=
  (measurement.eventTrace gates oracles classical services).foldr
    (fun current tail => DepthExpr.tensor (DepthExpr.atom current) tail)
    DepthExpr.id

/-- Evaluate strict terminal-measurement depth under an event assignment. -/
def evaluatedEventDepth {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (assign : Resource.Event (.quantum gates oracles classical services) → Nat)
    (measurement : TerminalZMeasure layout measuredQubits) : Nat :=
  DepthExpr.depthEval assign (measurement.eventDepth gates oracles classical services)

/-- Literal strict query depth of the descriptor-derived measurement event. -/
def eventQueryDepth {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (focus : Resource.Event (.quantum gates oracles classical services))
    (measurement : TerminalZMeasure layout measuredQubits) : Nat :=
  DepthExpr.queryDepthEval focus (measurement.eventDepth gates oracles classical services)

@[simp] theorem eventTrace_length {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    (measurement.eventTrace gates oracles classical services).length = measuredQubits := by
  simp [eventTrace]

@[simp] theorem ofList_eventTrace_eq_eventCost
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    ResourcePool.ofList (measurement.eventTrace gates oracles classical services) =
      (measurement.eventCost gates oracles classical services) := rfl

private theorem parallel_event_resources
    (events : List (Resource.Event (.quantum gates oracles classical services))) :
    DepthExpr.costEval (fun current => ResourcePool.singleton current)
        (events.foldr
          (fun current tail => DepthExpr.tensor (DepthExpr.atom current) tail)
          DepthExpr.id) =
      ResourcePool.ofList events := by
  induction events with
  | nil => rfl
  | cons current events ih =>
      by_cases hempty : events = [] <;> simp [hempty, ih]

/-- Linearizing the strict event-depth expression recovers the strict event
pool exactly. -/
@[simp] theorem resourcesFromEventDepth_eq_eventCost
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    DepthExpr.costEval (fun current => ResourcePool.singleton current)
        (measurement.eventDepth gates oracles classical services) =
      (measurement.eventCost gates oracles classical services) := by
  exact parallel_event_resources gates oracles classical services
      (measurement.eventTrace gates oracles classical services)

@[simp] theorem count_eventCost {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    ResourcePool.count (measurement.event gates oracles classical services)
      (measurement.eventCost gates oracles classical services) =
      measuredQubits := by
  simp [eventCost, eventTrace]

private theorem parallel_unit_event_depth
    (events : List (Resource.Event (.quantum gates oracles classical services))) :
    DepthExpr.depthEval (fun _ => 1)
        (events.foldr
          (fun current tail => DepthExpr.tensor (DepthExpr.atom current) tail)
          DepthExpr.id) =
      if events = [] then 0 else 1 := by
  induction events with
  | nil => rfl
  | cons current events ih =>
      by_cases hempty : events = [] <;> simp [hempty, ih]

private theorem parallel_self_event_query_depth
    (event : Resource.Event (.quantum gates oracles classical services)) (count : Nat) :
    DepthExpr.depthEval (DepthExpr.indicator event)
        ((List.replicate count event).foldr
          (fun current tail => DepthExpr.tensor (DepthExpr.atom current) tail)
          DepthExpr.id) =
      DepthExpr.depthEval (fun _ => 1)
        ((List.replicate count event).foldr
          (fun current tail => DepthExpr.tensor (DepthExpr.atom current) tail)
          DepthExpr.id) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, ih, DepthExpr.indicator_self]

@[simp] theorem empty_evaluatedEventDepth {totalQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout 0) :
    (measurement.evaluatedEventDepth gates oracles classical services) (fun _ => 1) = 0 := by
  rfl

@[simp] theorem nonempty_evaluatedEventDepth
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout (measuredQubits + 1)) :
    (measurement.evaluatedEventDepth gates oracles classical services) (fun _ => 1) = 1 := by
  simpa [evaluatedEventDepth, eventDepth, eventTrace] using
    parallel_unit_event_depth gates oracles classical services
      (measurement.eventTrace gates oracles classical services)

/-- Any positive-width terminal measurement is one all-one strict-event depth
layer.  This form avoids exposing a predecessor at module boundaries. -/
theorem evaluatedEventDepth_one_of_pos
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits)
    (positive : 0 < measuredQubits) :
    (measurement.evaluatedEventDepth gates oracles classical services) (fun _ => 1) = 1 := by
  obtain ⟨width, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact nonempty_evaluatedEventDepth gates oracles classical services measurement

/-- Querying the descriptor-derived event evaluates the same parallel layer as
the all-one event assignment, because every terminal occurrence has that one
sealed coordinate. -/
theorem eventQueryDepth_self
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout measuredQubits) :
    (measurement.eventQueryDepth gates oracles classical services)
      (measurement.event gates oracles classical services) =
      (measurement.evaluatedEventDepth gates oracles classical services) (fun _ => 1) := by
  unfold eventQueryDepth evaluatedEventDepth eventDepth eventTrace
  unfold DepthExpr.queryDepthEval
  exact parallel_self_event_query_depth gates oracles classical services
      (measurement.event gates oracles classical services) measuredQubits

@[simp] theorem empty_eventQueryDepth {totalQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout 0) :
    (measurement.eventQueryDepth gates oracles classical services)
      (measurement.event gates oracles classical services) = 0 := by
  rw [eventQueryDepth_self, empty_evaluatedEventDepth]

@[simp] theorem nonempty_eventQueryDepth
    {totalQubits measuredQubits : Nat}
    {layout : QubitLayout totalQubits}
    (measurement : TerminalZMeasure layout (measuredQubits + 1)) :
    (measurement.eventQueryDepth gates oracles classical services)
      (measurement.event gates oracles classical services) = 1 := by
  rw [eventQueryDepth_self, nonempty_evaluatedEventDepth]









@[simp] theorem zMeasure_systemIdx {qubitCount : Nat}
    (layout : QubitLayout qubitCount) :
    (zMeasure layout).systemIdx = layout.systemIdx := rfl























end TerminalZMeasure

end QuantumAlg

end
