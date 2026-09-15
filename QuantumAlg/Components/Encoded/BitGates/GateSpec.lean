/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.QubitPrimitive
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.NormNum
import all QuantumAlg.Components.Encoded.BitGates.Basic

/-!
# Encoded-bit gate specifications

This focused module is re-exported by `QuantumAlg.Components.EncodedBitGates`.
-/

section

namespace QuantumAlg

noncomputable section

namespace EncodedBit

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- One semantic encoded-bit base-gate operation, carrying the wire-disjointness
proofs required by the addressed primitive declaration. -/
inductive GateSpec (encoding : BinaryLabelEncoding Data) where
  /-- Flip one encoded semantic bit. -/
  | x (target : EncodedBit encoding)
  /-- Controlled flip between two encoded semantic bits. -/
  | cnot (control target : EncodedBit encoding)
      (hct : control.wire ≠ target.wire)
  /-- Double-controlled flip between three encoded semantic bits. -/
  | toffoli (controlA controlB target : EncodedBit encoding)
      (hab : controlA.wire ≠ controlB.wire)
      (ha : controlA.wire ≠ target.wire)
      (hb : controlB.wire ≠ target.wire)

namespace GateSpec

/-- Transport an encoded primitive across a semantic relabeling while keeping
its physical wires and strict event unchanged. -/
def relabel {Other : Type} (layout : Other ≃ Data) :
    GateSpec encoding → GateSpec (encoding.relabel layout)
  | .x target => .x (target.relabel layout)
  | .cnot control target hct =>
      .cnot (control.relabel layout) (target.relabel layout) hct
  | .toffoli controlA controlB target hab ha hb =>
      .toffoli (controlA.relabel layout) (controlB.relabel layout)
        (target.relabel layout) hab ha hb

/-- Strict event of one encoded-bit gate specification. Wire addresses and
disjointness proofs do not affect the event coordinate. -/
def event : GateSpec encoding → Resource.Event .quantum
  | .x _ => .gate (.builtin "x")
  | .cnot _ _ _ => .gate (.builtin "cnot")
  | .toffoli _ _ _ _ _ _ => .gate (.builtin "toffoli")

/-- Semantic relabeling preserves a primitive's strict event coordinate. -/
@[simp] theorem event_relabel {Other : Type} (layout : Other ≃ Data)
    (gate : GateSpec encoding) : event (relabel layout gate) = event gate := by
  cases gate <;> rfl

/-- Relabeling a complete literal gate list preserves its ordered strict event
trace. -/
theorem map_event_relabel {Other : Type} (layout : Other ≃ Data)
    (gates : List (GateSpec encoding)) :
    (gates.map (relabel layout)).map event = gates.map event := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change event (relabel layout gate) ::
          ((gates.map (relabel layout)).map event) =
        event gate :: gates.map event
      rw [event_relabel, ih]

/-- Right-associated symbolic depth of an ordered strict event trace. -/
def depthOfEvents : List (Resource.Event .quantum) →
    DepthExpr (Resource.Event .quantum)
  | [] => .id
  | event :: rest => .seq (.atom event) (depthOfEvents rest)







/-- Compile one encoded-bit operation directly to its actual circuit. -/
def program : GateSpec encoding → UnitaryCircuit (Qubits encoding.width)
  | x target => (QubitPrimitive.x target.wire).circuit
  | cnot control target hct =>
      (QubitPrimitive.cnot control.wire target.wire hct).circuit
  | toffoli controlA controlB target hab ha hb =>
      (QubitPrimitive.toffoli controlA.wire controlB.wire target.wire
        hab ha hb).circuit

/-- Direct compilation preserves the exact ordered primitive event. -/
@[simp] theorem program_eventTrace (gate : GateSpec encoding) :
    gate.program.eventTrace = [gate.event] := by
  cases gate <;> rfl

/-- Direct compilation charges exactly the declared primitive event. -/
@[simp] theorem program_eventCost (gate : GateSpec encoding) :
    gate.program.eventCost = ResourcePool.singleton gate.event := by
  cases gate <;> rfl

/-- Direct compilation exposes exactly one declared event-depth atom. -/
@[simp] theorem program_eventDepth (gate : GateSpec encoding) :
    gate.program.eventDepth = .atom gate.event := by
  cases gate <;> rfl

/-- One directly compiled encoded-bit primitive cannot emit an opaque
quantum-subroutine event. -/
theorem program_quantumSubroutine_count_zero
    (gate : GateSpec encoding) (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) gate.program.eventCost = 0 := by
  cases gate <;>
    change ResourcePool.count (.quantumSubroutine label)
      (ResourcePool.singleton (.gate _)) = 0 <;>
    exact ResourcePool.count_singleton_of_ne (by simp) 1

/-- One directly compiled encoded-bit primitive contributes exactly one
strict execution event. -/
theorem program_eventCost_card (gate : GateSpec encoding) :
    gate.program.eventCost.card = 1 := by
  cases gate <;>
    simp [program, QubitPrimitive.circuit, QubitPrimitive.leaf,
      QubitPrimitive.qubitPrimitiveLeafAt, ResourcePool.singleton]

/-- A strict gate coordinate distinct from X, CNOT, and Toffoli cannot occur
in one encoded-bit primitive. -/
theorem program_gate_count_zero_of_ne
    (gate : GateSpec encoding) (label : Resource.GateLabel)
    (hx : label ≠ .builtin "x")
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label) gate.program.eventCost = 0 := by
  cases gate with
  | x target =>
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        injection equality with equality
        exact hx equality) 1
  | cnot control target hct =>
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        injection equality with equality
        exact hcnot equality) 1
  | toffoli controlA controlB target hab ha hb =>
      exact ResourcePool.count_singleton_of_ne (by
        intro equality
        injection equality with equality
        exact htoffoli equality) 1

/-- Every physical wire of one compiled encoded-bit gate lies in the
canonical range of its semantic encoding. -/
theorem program_physical_idx_subset_range (gate : GateSpec encoding) :
    gate.program.physical_idx ⊆ List.range encoding.width := by
  cases gate with
  | x target =>
      exact QubitPrimitive.systemIdx_subset_range
        (QubitPrimitive.x target.wire)
  | cnot control target hct =>
      exact QubitPrimitive.systemIdx_subset_range
        (QubitPrimitive.cnot control.wire target.wire hct)
  | toffoli controlA controlB target hab ha hb =>
      exact QubitPrimitive.systemIdx_subset_range
        (QubitPrimitive.toffoli controlA.wire controlB.wire target.wire
          hab ha hb)





/-- Semantic action of one encoded-bit operation. -/
def step : GateSpec encoding → Data → Data
  | x target => target.flip
  | cnot control target _hct => cnotStep control target
  | toffoli controlA controlB target _hab _ha _hb =>
      toffoliStep controlA controlB target

/-- Semantic relabeling conjugates the primitive action by the supplied
layout equivalence. -/
theorem step_relabel {Other : Type} (layout : Other ≃ Data)
    (gate : GateSpec encoding) (x : Other) :
    (relabel layout gate).step x = layout.symm (gate.step (layout x)) := by
  cases gate with
  | x target => rfl
  | cnot control target hct =>
      by_cases hcontrol : control.get (layout x)
      · simp [relabel, step, EncodedBit.relabel, EncodedBit.cnotStep,
          hcontrol]
      · simp [relabel, step, EncodedBit.relabel, EncodedBit.cnotStep,
          hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      by_cases hcontrols :
          controlA.get (layout x) && controlB.get (layout x)
      · simp [relabel, step, EncodedBit.relabel, EncodedBit.toffoliStep,
          hcontrols]
      · simp [relabel, step, EncodedBit.relabel, EncodedBit.toffoliStep,
          hcontrols]

/-- Every encoded-bit gate-spec semantic step is self-inverse. -/
theorem step_step (gate : GateSpec encoding) (x : Data) :
    gate.step (gate.step x) = x := by
  cases gate with
  | x target =>
      exact EncodedBit.flip_flip target x
  | cnot control target hct =>
      exact EncodedBit.cnotStep_cnotStep control target hct x
  | toffoli controlA controlB target _hab ha hb =>
      exact EncodedBit.toffoliStep_toffoliStep controlA controlB target ha hb x

/-- A gate preserves a projection when its target flip preserves that
projection.  Controls may be inspected, but only the target bit is written. -/
def targetFlipPreserves {α : Type} (project : Data → α) :
    GateSpec encoding → Prop
  | x target => ∀ y, project (target.flip y) = project y
  | cnot _ target _ => ∀ y, project (target.flip y) = project y
  | toffoli _ _ target _ _ _ => ∀ y, project (target.flip y) = project y

/-- One encoded-bit operation preserves a projection if its target flip
preserves that projection. -/
theorem step_preserves_of_targetFlipPreserves {α : Type}
    {project : Data → α} (gate : GateSpec encoding)
    (h : targetFlipPreserves project gate) (x : Data) :
    project (gate.step x) = project x := by
  cases gate with
  | x target =>
      exact h x
  | cnot control target hct =>
      unfold step cnotStep
      by_cases hcontrol : control.get x
      · simpa [hcontrol] using h x
      · simp [hcontrol]
  | toffoli controlA controlB target hab ha hb =>
      unfold step toffoliStep
      by_cases hcontrols : controlA.get x && controlB.get x
      · simpa [hcontrols] using h x
      · simp [hcontrols]

/-- A gate is wire-disjoint from an observed bit when the observed wire is none
of the wires the gate reads or writes. -/
def bitDisjoint (observed : EncodedBit encoding) :
    GateSpec encoding -> Prop
  | x target => target.wire ≠ observed.wire
  | cnot control target _ =>
      control.wire ≠ observed.wire ∧ target.wire ≠ observed.wire
  | toffoli controlA controlB target _ _ _ =>
      controlA.wire ≠ observed.wire ∧ controlB.wire ≠ observed.wire ∧
        target.wire ≠ observed.wire

/-- A gate whose read/write wires are disjoint from an observed bit commutes
with flipping that observed bit. -/
theorem step_flip_comm_of_bitDisjoint
    (gate : GateSpec encoding) (observed : EncodedBit encoding)
    (h : bitDisjoint observed gate) (x : Data) :
    gate.step (observed.flip x) =
      observed.flip (gate.step x) := by
  cases gate with
  | x target =>
      exact EncodedBit.flip_comm target observed x
  | cnot control target _hct =>
      rcases h with ⟨hcontrol, _htarget⟩
      have hcontrolGet :
          control.get (observed.flip x) = control.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed control
          (Ne.symm hcontrol)]
      change EncodedBit.cnotStep control target (observed.flip x) =
        observed.flip (EncodedBit.cnotStep control target x)
      unfold EncodedBit.cnotStep
      rw [hcontrolGet]
      by_cases hc : control.get x
      · simp [hc, EncodedBit.flip_comm target observed x]
      · simp [hc]
  | toffoli controlA controlB target _hab _ha _hb =>
      rcases h with ⟨hcontrolA, hcontrolB, _htarget⟩
      have hcontrolAGet :
          controlA.get (observed.flip x) = controlA.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed controlA
          (Ne.symm hcontrolA)]
      have hcontrolBGet :
          controlB.get (observed.flip x) = controlB.get x := by
        rw [EncodedBit.get_flip_of_wire_ne observed controlB
          (Ne.symm hcontrolB)]
      change EncodedBit.toffoliStep controlA controlB target
          (observed.flip x) =
        observed.flip (EncodedBit.toffoliStep controlA controlB target x)
      unfold EncodedBit.toffoliStep
      rw [hcontrolAGet, hcontrolBGet]
      by_cases hc : controlA.get x && controlB.get x
      · simp [hc, EncodedBit.flip_comm target observed x]
      · simp [hc]

/-- A gate whose read/write wires are disjoint from an observed bit preserves
that bit's readout. -/
theorem step_get_of_bitDisjoint
    (gate : GateSpec encoding) (observed : EncodedBit encoding)
    (h : bitDisjoint observed gate) (x : Data) :
    observed.get (gate.step x) = observed.get x := by
  cases gate with
  | x target =>
      exact EncodedBit.get_flip_of_wire_ne target observed h x
  | cnot control target _hct =>
      exact EncodedBit.cnotStep_get_of_target_ne control target observed h.2 x
  | toffoli controlA controlB target _hab _ha _hb =>
      exact EncodedBit.toffoliStep_get_of_target_ne
        controlA controlB target observed h.2.2 x

/-- One encoded-bit operation realizes its semantic action. -/
theorem realizes (gate : GateSpec encoding) :
    UnitaryCircuit.Realizes encoding gate.program gate.step := by
  cases gate with
  | x target =>
      exact x_realizes target
  | cnot control target hct =>
      exact cnot_realizes control target hct
  | toffoli controlA controlB target hab ha hb =>
      exact toffoli_realizes controlA controlB target hab ha hb

/-- Compile a gate-spec list directly to one actual circuit in list execution
order.  The recursion remains right-associated so its symbolic depth tree is
the same right fold as the source schedule. -/
def programList : List (GateSpec encoding) →
    UnitaryCircuit (Qubits encoding.width)
  | [] => UnitaryCircuit.identity (Qubits encoding.width) [] (by simp)
  | gate :: rest => UnitaryCircuit.seq gate.program (programList rest)

/-- The ordered circuit trace is exactly the mapped GateSpec event schedule. -/
@[simp] theorem programList_eventTrace (gates : List (GateSpec encoding)) :
    (programList gates).eventTrace = gates.map event := by
  induction gates with
  | nil => rfl
  | cons gate rest ih => simp [programList, ih]

/-- The circuit event pool is the literal multiset of the GateSpec schedule. -/
@[simp] theorem programList_eventCost (gates : List (GateSpec encoding)) :
    (programList gates).eventCost = ResourcePool.ofList (gates.map event) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, programList_eventTrace]

/-- The circuit event critical path is the ordered GateSpec event schedule. -/
@[simp] theorem programList_eventDepth (gates : List (GateSpec encoding)) :
    (programList gates).eventDepth = depthOfEvents (gates.map event) := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change DepthExpr.seq gate.program.eventDepth
          (programList rest).eventDepth = DepthExpr.seq _ _
      rw [program_eventDepth, ih]

/-- A directly compiled encoded-bit gate list cannot emit an opaque
quantum-subroutine event.  This is derived from the same primitive circuits
that execute the list, rather than from a separately supplied resource pool. -/
theorem programList_quantumSubroutine_count_zero
    (gates : List (GateSpec encoding))
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (programList gates).eventCost = 0 := by
  induction gates with
  | nil => simp [programList]
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        program_quantumSubroutine_count_zero, ih]

/-- The strict event ledger of a compiled gate list has one occurrence per
source GateSpec. -/
theorem programList_eventCost_card
    (gates : List (GateSpec encoding)) :
    (programList gates).eventCost.card = gates.length := by
  rw [programList_eventCost]
  simp [ResourcePool.ofList]

/-- Under unit primitive durations, the strict sequential depth of a compiled
gate list is exactly its source-list length. -/
@[simp] theorem programList_evaluatedEventDepth_unit
    (gates : List (GateSpec encoding)) :
    (programList gates).evaluatedEventDepth (fun _ => 1) = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change gate.program.evaluatedEventDepth (fun _ => 1) +
          (programList rest).evaluatedEventDepth (fun _ => 1) =
        rest.length + 1
      rw [ih]
      have hgate : gate.program.evaluatedEventDepth (fun _ => 1) = 1 := by
        simp [UnitaryCircuit.evaluatedEventDepth]
      rw [hgate]
      omega

/-- Indicator that one encoded-bit primitive emits a selected strict event.
This is the list-level bridge used when a client needs a gate-coordinate count
rather than the total primitive envelope. -/
def eventMultiplicity (focus : Resource.Event .quantum)
    (gate : GateSpec encoding) : Nat :=
  if event gate = focus then 1 else 0

/-- Equal strict events have equal selected-coordinate indicators. -/
theorem eventMultiplicity_eq_of_event_eq
    (focus : Resource.Event .quantum) {left right : GateSpec encoding}
    (h : event left = event right) :
    eventMultiplicity focus left = eventMultiplicity focus right := by
  simp [eventMultiplicity, h]

/-- Equal strict event schedules have equal sums for every selected gate
coordinate. -/
theorem sum_eventMultiplicity_eq_of_events_eq
    (focus : Resource.Event .quantum)
    {Left Right : Type}
    {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)}
    {right : List (GateSpec rightEncoding)}
    (h : left.map event = right.map event) :
    (left.map (eventMultiplicity focus)).sum =
      (right.map (eventMultiplicity focus)).sum := by
  have hmap :
      left.map (eventMultiplicity focus) =
        (left.map event).map fun emitted => if emitted = focus then 1 else 0 := by
    simp [eventMultiplicity, List.map_map, Function.comp_def]
  have hmap' :
      right.map (eventMultiplicity focus) =
        (right.map event).map fun emitted => if emitted = focus then 1 else 0 := by
    simp [eventMultiplicity, List.map_map, Function.comp_def]
  rw [hmap, hmap', h]

/-- A selected strict-event multiplicity is the sum of its per-gate indicators
over the actual source list compiled by `programList`. -/
theorem programList_event_count_eq_sum_eventMultiplicity
    (focus : Resource.Event .quantum) (gates : List (GateSpec encoding)) :
    ResourcePool.count focus (programList gates).eventCost =
      (gates.map (eventMultiplicity focus)).sum := by
  rw [programList_eventCost, ResourcePool.count_ofList]
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.map_cons, List.sum_cons, List.count_cons]
      rw [ih]
      simp [eventMultiplicity, Nat.add_comm]

/-- Per-source-gate multiplicity of the strict X coordinate. -/
def xMultiplicity (gate : GateSpec encoding) : Nat :=
  eventMultiplicity (.gate (.builtin "x")) gate

/-- Per-source-gate multiplicity of the strict CNOT coordinate. -/
def cnotMultiplicity (gate : GateSpec encoding) : Nat :=
  eventMultiplicity (.gate (.builtin "cnot")) gate

/-- Per-source-gate multiplicity of the strict Toffoli coordinate. -/
def toffoliMultiplicity (gate : GateSpec encoding) : Nat :=
  eventMultiplicity (.gate (.builtin "toffoli")) gate

theorem sum_xMultiplicity_eq_of_events_eq
    {Left Right : Type}
    {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)}
    {right : List (GateSpec rightEncoding)}
    (h : left.map event = right.map event) :
    (left.map xMultiplicity).sum = (right.map xMultiplicity).sum := by
  unfold xMultiplicity
  exact sum_eventMultiplicity_eq_of_events_eq _ h

theorem sum_cnotMultiplicity_eq_of_events_eq
    {Left Right : Type}
    {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)}
    {right : List (GateSpec rightEncoding)}
    (h : left.map event = right.map event) :
    (left.map cnotMultiplicity).sum = (right.map cnotMultiplicity).sum := by
  unfold cnotMultiplicity
  exact sum_eventMultiplicity_eq_of_events_eq _ h

theorem sum_toffoliMultiplicity_eq_of_events_eq
    {Left Right : Type}
    {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)}
    {right : List (GateSpec rightEncoding)}
    (h : left.map event = right.map event) :
    (left.map toffoliMultiplicity).sum =
      (right.map toffoliMultiplicity).sum := by
  unfold toffoliMultiplicity
  exact sum_eventMultiplicity_eq_of_events_eq _ h

@[simp] theorem xMultiplicity_x (target : EncodedBit encoding) :
    xMultiplicity (.x target) = 1 := rfl

@[simp] theorem xMultiplicity_cnot (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    xMultiplicity (.cnot control target hne) = 0 := rfl

@[simp] theorem xMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    xMultiplicity (.toffoli controlA controlB target hab ha hb) = 0 := rfl

@[simp] theorem cnotMultiplicity_x (target : EncodedBit encoding) :
    cnotMultiplicity (.x target) = 0 := rfl

@[simp] theorem cnotMultiplicity_cnot
    (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    cnotMultiplicity (.cnot control target hne) = 1 := rfl

@[simp] theorem cnotMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    cnotMultiplicity (.toffoli controlA controlB target hab ha hb) = 0 := rfl

@[simp] theorem toffoliMultiplicity_x (target : EncodedBit encoding) :
    toffoliMultiplicity (.x target) = 0 := rfl

@[simp] theorem toffoliMultiplicity_cnot
    (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    toffoliMultiplicity (.cnot control target hne) = 0 := rfl

@[simp] theorem toffoliMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    toffoliMultiplicity (.toffoli controlA controlB target hab ha hb) = 1 := rfl

/-- Every encoded-bit gate is exactly one X, CNOT, or Toffoli leaf, so the
physical list length is the sum of those three strict coordinates. -/
theorem length_eq_multiplicity_sums (gates : List (GateSpec encoding)) :
    gates.length =
      (gates.map xMultiplicity).sum +
        (gates.map cnotMultiplicity).sum +
        (gates.map toffoliMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      cases gate <;> simp [ih] <;> omega

/-- Coordinate-specific X count for a compiled GateSpec source list. -/
theorem programList_x_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (.gate (.builtin "x"))
        (programList gates).eventCost =
      (gates.map xMultiplicity).sum :=
  programList_event_count_eq_sum_eventMultiplicity _ gates

/-- Coordinate-specific CNOT count for a compiled GateSpec source list. -/
theorem programList_cnot_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (.gate (.builtin "cnot"))
        (programList gates).eventCost =
      (gates.map cnotMultiplicity).sum :=
  programList_event_count_eq_sum_eventMultiplicity _ gates

/-- Coordinate-specific Toffoli count for a compiled GateSpec source list. -/
theorem programList_toffoli_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (.gate (.builtin "toffoli"))
        (programList gates).eventCost =
      (gates.map toffoliMultiplicity).sum :=
  programList_event_count_eq_sum_eventMultiplicity _ gates

/-- A coordinate outside the encoded-bit X/CNOT/Toffoli language has zero
multiplicity in every directly compiled gate list. -/
theorem programList_gate_count_zero_of_ne
    (gates : List (GateSpec encoding)) (label : Resource.GateLabel)
    (hx : label ≠ .builtin "x")
    (hcnot : label ≠ .builtin "cnot")
    (htoffoli : label ≠ .builtin "toffoli") :
    ResourcePool.count (.gate label) (programList gates).eventCost = 0 := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        program_gate_count_zero_of_ne gate label hx hcnot htoffoli, ih,
        Nat.zero_add]

/-- A compiled gate list never addresses a physical wire outside its encoded
register. -/
theorem programList_physical_idx_subset_range
    (gates : List (GateSpec encoding)) :
    (programList gates).physical_idx ⊆ List.range encoding.width := by
  induction gates with
  | nil =>
      intro index hindex
      simp [programList, UnitaryCircuit.identity] at hindex
  | cons gate rest ih =>
      intro index hindex
      change index ∈ UnitaryCircuit.unionPhysicalIdx
        gate.program.physical_idx (programList rest).physical_idx at hindex
      change index ∈ gate.program.physical_idx ∪
        (programList rest).physical_idx at hindex
      exact (List.mem_union_iff.mp hindex).elim
        (fun hgate => program_physical_idx_subset_range gate hgate)
        (fun hrest => ih hrest)



/-- Exact count of the three strict event coordinates emitted by encoded-bit
primitive compilation. Unlike collection cardinality, this definition states
the target event predicate explicitly. -/
def primitiveEventCount {R : Register} (circuit : UnitaryCircuit R) : Nat :=
  ResourcePool.count (.gate (.builtin "x")) circuit.eventCost +
    ResourcePool.count (.gate (.builtin "cnot")) circuit.eventCost +
    ResourcePool.count (.gate (.builtin "toffoli")) circuit.eventCost

/-- Compiling a GateSpec list creates exactly one targeted primitive event per
source gate. -/
@[simp] theorem primitiveEventCount_programList
    (gates : List (GateSpec encoding)) :
    primitiveEventCount (programList gates) = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      unfold primitiveEventCount at ih ⊢
      rw [programList, UnitaryCircuit.seq_eventCost, program_eventCost]
      simp only [ResourcePool.count_add, List.length_cons]
      cases gate with
      | x target =>
          simp only [event, ResourcePool.count_singleton_self]
          rw [ResourcePool.count_singleton_of_ne (by decide),
            ResourcePool.count_singleton_of_ne (by decide)]
          omega
      | cnot control target hct =>
          simp only [event, ResourcePool.count_singleton_self]
          rw [ResourcePool.count_singleton_of_ne (by decide),
            ResourcePool.count_singleton_of_ne (by decide)]
          omega
      | toffoli controlA controlB target hab ha hb =>
          simp only [event, ResourcePool.count_singleton_self]
          rw [ResourcePool.count_singleton_of_ne (by decide),
            ResourcePool.count_singleton_of_ne (by decide)]
          omega















/-- Equal ordered strict-event schedules have equal compiled event pools. -/
theorem programList_eventCost_eq_of_events_eq
    (left right : List (GateSpec encoding))
    (hevents : left.map event = right.map event) :
    (programList left).eventCost = (programList right).eventCost := by
  rw [programList_eventCost, programList_eventCost, hevents]

/-- Equal ordered strict-event schedules have equal compiled event paths. -/
theorem programList_eventDepth_eq_of_events_eq
    (left right : List (GateSpec encoding))
    (hevents : left.map event = right.map event) :
    (programList left).eventDepth = (programList right).eventDepth := by
  rw [programList_eventDepth, programList_eventDepth, hevents]

/-- Semantic action of a list of encoded-bit operations, in list execution
order. -/
def stepList : List (GateSpec encoding) → Data → Data
  | [] => id
  | gate :: rest => fun x => stepList rest (gate.step x)

/-- Relabeling every primitive conjugates the complete list fold by the same
semantic layout equivalence. -/
theorem stepList_relabel {Other : Type} (layout : Other ≃ Data) :
    ∀ (gates : List (GateSpec encoding)) (state : Other),
      stepList (gates.map (relabel layout)) state =
        layout.symm (stepList gates (layout state))
  | [], state => by simp [stepList]
  | gate :: rest, state => by
      change stepList (rest.map (relabel layout))
          ((relabel layout gate).step state) = _
      rw [step_relabel]
      rw [stepList_relabel layout rest]
      simp only [Equiv.apply_symm_apply]
      rfl

/-- A gate list preserves a projection if every gate target flip preserves it. -/
theorem stepList_preserves_of_targetFlipPreserves {α : Type}
    {project : Data → α} (gates : List (GateSpec encoding))
    (h :
      ∀ gate, gate ∈ gates → targetFlipPreserves project gate)
    (x : Data) :
    project (stepList gates x) = project x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change project (stepList rest (gate.step x)) = project x
      calc
        project (stepList rest (gate.step x)) = project (gate.step x) :=
          ih (fun next hnext => h next (by simp [hnext])) (gate.step x)
        _ = project x :=
          step_preserves_of_targetFlipPreserves gate (h gate (by simp)) x

/-- A gate list disjoint from one observed bit preserves that bit's readout. -/
theorem stepList_get_of_bitDisjoint
    (gates : List (GateSpec encoding)) (observed : EncodedBit encoding)
    (h : ∀ gate, gate ∈ gates → bitDisjoint observed gate)
    (x : Data) :
    observed.get (stepList gates x) = observed.get x := by
  induction gates generalizing x with
  | nil => rfl
  | cons gate rest ih =>
      simp only [stepList]
      rw [ih (fun next hnext => h next (by simp [hnext]))]
      exact step_get_of_bitDisjoint gate observed (h gate (by simp)) x

/-- A gate list whose read/write wires are all disjoint from an observed bit
commutes with flipping that observed bit. -/
theorem stepList_flip_comm_of_bitDisjoint
    (gates : List (GateSpec encoding)) (observed : EncodedBit encoding)
    (h : ∀ gate, gate ∈ gates -> bitDisjoint observed gate)
    (x : Data) :
    stepList gates (observed.flip x) =
      observed.flip (stepList gates x) := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change stepList rest (gate.step (observed.flip x)) =
        observed.flip (stepList rest (gate.step x))
      rw [step_flip_comm_of_bitDisjoint gate observed (h gate (by simp)) x]
      exact ih (fun next hnext => h next (by simp [hnext])) (gate.step x)

/-- Splitting a gate list at append corresponds to sequential semantic
composition in list execution order. -/
theorem stepList_append (first second : List (GateSpec encoding)) (x : Data) :
    stepList (first ++ second) x = stepList second (stepList first x) := by
  induction first generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- Reversing a gate list gives a right inverse for its semantic step. -/
theorem stepList_reverse_stepList
    (gates : List (GateSpec encoding)) (x : Data) :
    stepList gates.reverse (stepList gates x) = x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp only [List.reverse_cons]
      rw [stepList_append]
      change gate.step (stepList rest.reverse (stepList rest (gate.step x))) = x
      rw [ih (gate.step x)]
      exact step_step gate x

/-- The recursive gate-list semantics agrees with a left fold over gates. -/
theorem stepList_eq_foldl (gates : List (GateSpec encoding)) (x : Data) :
    stepList gates x = gates.foldl (fun y gate => gate.step y) x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- A list of encoded-bit operations realizes its folded semantic action. -/
theorem realizesList (gates : List (GateSpec encoding)) :
    UnitaryCircuit.Realizes encoding (programList gates) (stepList gates) := by
  induction gates with
  | nil =>
      simpa [programList, stepList] using UnitaryCircuit.Realizes.identity encoding
  | cons gate rest ih =>
      simpa [programList, stepList] using
        UnitaryCircuit.Realizes.seq
          (firstStep := gate.step) (secondStep := stepList rest)
          (realizes gate) ih

/-- A gate list realizes any step pointwise equal to its folded semantic
action. -/
theorem realizesList_congrStep (gates : List (GateSpec encoding))
    {step : Data -> Data}
    (hstep : ∀ x, stepList gates x = step x) :
    UnitaryCircuit.Realizes encoding (programList gates) step where
  apply_encoded_ket := by
    intro x
    rw [(realizesList gates).apply_encoded_ket x]
    rw [hstep x]

/-- Proof that the actual compiled list realizes its folded semantic step. -/
theorem witnessList (gates : List (GateSpec encoding)) :
    UnitaryCircuit.Realizes encoding (programList gates) (stepList gates) :=
  realizesList gates

/-- A clean-work controlled version of one encoded-bit gate.  X becomes CNOT,
CNOT becomes Toffoli, and Toffoli is implemented by compute-control-uncompute
through the supplied work bit. -/
def controlledWithWorkGates
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    List (GateSpec encoding) :=
  match gate with
  | x target =>
      [GateSpec.cnot control target (Ne.symm hcontrol)]
  | cnot source target hsourceTarget =>
      [GateSpec.toffoli control source target (Ne.symm hcontrol.1)
        (Ne.symm hcontrol.2) hsourceTarget]
  | toffoli sourceA sourceB target hsourceAB _hsourceATarget _hsourceBTarget =>
      [ GateSpec.toffoli sourceA sourceB work
          hsourceAB hwork.1 hwork.2.1
      , GateSpec.toffoli control work target
          hcontrolWork (Ne.symm hcontrol.2.2) (Ne.symm hwork.2.2)
      , GateSpec.toffoli sourceA sourceB work
          hsourceAB hwork.1 hwork.2.1 ]

/-- Clean-work control expands one physical primitive to at most three
physical primitives. -/
theorem controlledWithWorkGates_length_le_three
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledWithWorkGates control work gate hcontrol hwork
      hcontrolWork).length ≤ 3 := by
  cases gate <;> simp [controlledWithWorkGates]

/-- Adding a clean external control and work bit preserves disjointness from
an unrelated observed bit. -/
theorem controlledWithWorkGates_bitDisjoint
    (control work observed : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (hworkObserved : work.wire ≠ observed.wire)
    (hgateObserved : bitDisjoint observed gate) :
    ∀ emitted,
      emitted ∈ controlledWithWorkGates control work gate hcontrol hwork
          hcontrolWork →
        bitDisjoint observed emitted := by
  intro emitted hemitted
  cases gate <;>
    simp only [controlledWithWorkGates, List.mem_cons, List.not_mem_nil,
      or_false] at hemitted
  · subst emitted
    exact ⟨hcontrolObserved, hgateObserved⟩
  · subst emitted
    exact ⟨hcontrolObserved, hgateObserved.1, hgateObserved.2⟩
  · rcases hemitted with rfl | rfl | rfl
    · exact ⟨hgateObserved.1, hgateObserved.2.1, hworkObserved⟩
    · exact ⟨hcontrolObserved, hworkObserved, hgateObserved.2.2⟩
    · exact ⟨hgateObserved.1, hgateObserved.2.1, hworkObserved⟩

/-- Strict event expansion induced by one clean-work control lift. -/
def controlledEventExpansion : GateSpec encoding →
    List (Resource.Event .quantum)
  | .x _ => [.gate (.builtin "cnot")]
  | .cnot _ _ _ => [.gate (.builtin "toffoli")]
  | .toffoli _ _ _ _ _ _ =>
      [.gate (.builtin "toffoli"), .gate (.builtin "toffoli"),
        .gate (.builtin "toffoli")]

/-- The controlled gate list exposes exactly the source gate's strict event
expansion, independently of wire addresses and proof fields. -/
theorem map_event_controlledWithWorkGates
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledWithWorkGates control work gate hcontrol hwork
        hcontrolWork).map event = controlledEventExpansion gate := by
  cases gate <;> rfl





/-- Semantic action of `controlledWithWorkGates`. -/
def controlledWithWorkStep
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    Data -> Data :=
  stepList (controlledWithWorkGates control work gate hcontrol hwork
    hcontrolWork)

/-- Direct realization proof for one clean-work controlled encoded-bit gate. -/
theorem controlledWithWorkWitness
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    UnitaryCircuit.Realizes encoding
      (programList
        (controlledWithWorkGates control work gate hcontrol hwork hcontrolWork))
      (controlledWithWorkStep control work gate hcontrol hwork hcontrolWork) :=
  witnessList (controlledWithWorkGates control work gate hcontrol hwork
    hcontrolWork)

/-- If the extra control is false, the clean-work controlled gate is a no-op. -/
theorem controlledWithWorkStep_eq_self_of_control_false
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolFalse : control.get x = false) :
    controlledWithWorkStep control work gate hcontrol hwork hcontrolWork x =
      x := by
  cases gate with
  | x target =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, hcontrolFalse]
  | cnot source target hsourceTarget =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.toffoliStep, hcontrolFalse]
  | toffoli sourceA sourceB target hsourceAB hsourceATarget hsourceBTarget =>
      simp only [controlledWithWorkStep, controlledWithWorkGates, stepList,
        step, id_eq]
      let y := EncodedBit.toffoliStep sourceA sourceB work x
      have hcontrolY : control.get y = false := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
          control (Ne.symm hcontrolWork)]
        exact hcontrolFalse
      change
        EncodedBit.toffoliStep sourceA sourceB work
          (EncodedBit.toffoliStep control work target y) = x
      have hmiddle : EncodedBit.toffoliStep control work target y = y := by
        unfold EncodedBit.toffoliStep
        rw [if_neg (by simp [hcontrolY])]
      rw [hmiddle]
      dsimp [y]
      exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
        hwork.1 hwork.2.1 x

/-- If the extra control is true and the work bit starts clean, the clean-work
controlled gate acts like the original gate. -/
theorem controlledWithWorkStep_eq_step_of_control_true
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolTrue : control.get x = true)
    (hworkClean : work.get x = false) :
    controlledWithWorkStep control work gate hcontrol hwork hcontrolWork x =
      gate.step x := by
  cases gate with
  | x target =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, hcontrolTrue]
  | cnot source target hsourceTarget =>
      simp [controlledWithWorkStep, controlledWithWorkGates, stepList, step,
        EncodedBit.cnotStep, EncodedBit.toffoliStep, hcontrolTrue]
  | toffoli sourceA sourceB target hsourceAB hsourceATarget hsourceBTarget =>
      simp only [controlledWithWorkStep, controlledWithWorkGates, stepList,
        step, id_eq]
      let y := EncodedBit.toffoliStep sourceA sourceB work x
      have hcontrolY : control.get y = true := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
          control (Ne.symm hcontrolWork)]
        exact hcontrolTrue
      have hworkY :
          work.get y = (sourceA.get x && sourceB.get x) := by
        dsimp [y]
        rw [EncodedBit.toffoliStep_get_target]
        cases sourceA.get x <;> cases sourceB.get x <;> simp [hworkClean]
      change
        EncodedBit.toffoliStep sourceA sourceB work
          (EncodedBit.toffoliStep control work target y) =
        EncodedBit.toffoliStep sourceA sourceB target x
      by_cases hcontrols : sourceA.get x && sourceB.get x
      · have hmiddle :
            EncodedBit.toffoliStep control work target y = target.flip y := by
          unfold EncodedBit.toffoliStep
          rw [if_pos (by simp [hcontrolY, hworkY, hcontrols])]
        have htargetWork :
            EncodedBit.toffoliStep sourceA sourceB work (target.flip y) =
              work.flip (target.flip y) := by
          unfold EncodedBit.toffoliStep
          have ha :
              sourceA.get (target.flip y) = sourceA.get x := by
            rw [EncodedBit.get_flip_of_wire_ne target sourceA
              (Ne.symm hsourceATarget)]
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceA (Ne.symm hwork.1)]
          have hb :
              sourceB.get (target.flip y) = sourceB.get x := by
            rw [EncodedBit.get_flip_of_wire_ne target sourceB
              (Ne.symm hsourceBTarget)]
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceB (Ne.symm hwork.2.1)]
          rw [if_pos (by simpa [ha, hb] using hcontrols)]
        have horig :
            EncodedBit.toffoliStep sourceA sourceB target x =
              target.flip x := by
          unfold EncodedBit.toffoliStep
          rw [if_pos hcontrols]
        rw [hmiddle, htargetWork, horig]
        rw [EncodedBit.flip_comm work target y]
        have hworkUndo : work.flip y = x := by
          have hsourceAY : sourceA.get y = sourceA.get x := by
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceA (Ne.symm hwork.1)]
          have hsourceBY : sourceB.get y = sourceB.get x := by
            dsimp [y]
            rw [EncodedBit.toffoliStep_get_of_target_ne sourceA sourceB work
              sourceB (Ne.symm hwork.2.1)]
          have hcontrolsY : sourceA.get y && sourceB.get y := by
            simpa [hsourceAY, hsourceBY] using hcontrols
          have htoffoliY :
              EncodedBit.toffoliStep sourceA sourceB work y =
                work.flip y := by
            unfold EncodedBit.toffoliStep
            rw [if_pos hcontrolsY]
          rw [← htoffoliY]
          dsimp [y]
          exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
            hwork.1 hwork.2.1 x
        rw [hworkUndo]
      · have hmiddle :
            EncodedBit.toffoliStep control work target y = y := by
          unfold EncodedBit.toffoliStep
          rw [if_neg (by simp [hcontrolY, hworkY, hcontrols])]
        rw [hmiddle]
        have houter :
            EncodedBit.toffoliStep sourceA sourceB work y = x := by
          dsimp [y]
          exact EncodedBit.toffoliStep_toffoliStep sourceA sourceB work
            hwork.1 hwork.2.1 x
        have horig :
            EncodedBit.toffoliStep sourceA sourceB target x = x := by
          unfold EncodedBit.toffoliStep
          rw [if_neg hcontrols]
        rw [houter, horig]

/-- Clean-work controlled version of a list of encoded-bit gates. -/
def controlledListWithWorkGates
    (control work : EncodedBit encoding) :
    (gates : List (GateSpec encoding)) ->
    (∀ gate, gate ∈ gates -> bitDisjoint control gate) ->
    (∀ gate, gate ∈ gates -> bitDisjoint work gate) ->
    (hcontrolWork : control.wire ≠ work.wire) ->
    List (GateSpec encoding)
  | [], _hcontrol, _hwork, _hcontrolWork => []
  | gate :: rest, hcontrol, hwork, hcontrolWork =>
      controlledWithWorkGates control work gate
        (hcontrol gate (by simp)) (hwork gate (by simp)) hcontrolWork ++
      controlledListWithWorkGates control work rest
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        hcontrolWork

/-- Controlling a gate list with clean work preserves disjointness from an
unrelated observed bit. -/
theorem controlledListWithWorkGates_bitDisjoint
    (control work observed : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire)
    (hcontrolObserved : control.wire ≠ observed.wire)
    (hworkObserved : work.wire ≠ observed.wire)
    (hgatesObserved :
      ∀ gate, gate ∈ gates → bitDisjoint observed gate) :
    ∀ emitted,
      emitted ∈ controlledListWithWorkGates control work gates hcontrol
          hwork hcontrolWork →
        bitDisjoint observed emitted := by
  induction gates with
  | nil => simp [controlledListWithWorkGates]
  | cons gate rest ih =>
      intro emitted hemitted
      rw [controlledListWithWorkGates, List.mem_append] at hemitted
      rcases hemitted with hhead | htail
      · exact controlledWithWorkGates_bitDisjoint control work observed gate
          (hcontrol gate (by simp)) (hwork gate (by simp)) hcontrolWork
          hcontrolObserved hworkObserved
          (hgatesObserved gate (by simp)) emitted hhead
      · exact ih
          (fun next hnext => hcontrol next (by simp [hnext]))
          (fun next hnext => hwork next (by simp [hnext]))
          (fun next hnext => hgatesObserved next (by simp [hnext]))
          emitted htail

/-- Controlling a list with one clean work bit increases physical leaf count
by at most a factor of three. -/
theorem controlledListWithWorkGates_length_le_three_mul
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledListWithWorkGates control work gates hcontrol hwork
      hcontrolWork).length ≤ 3 * gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.length_append]
      have hhead := controlledWithWorkGates_length_le_three
        control work gate (hcontrol gate (by simp)) (hwork gate (by simp))
        hcontrolWork
      have htail := ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
      simp only [List.length_cons]
      omega

/-- Exact physical leaf count of a clean-work control lift: every source
Toffoli expands from one gate to three, while X and CNOT remain one gate. -/
theorem controlledListWithWorkGates_length_eq
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledListWithWorkGates control work gates hcontrol hwork
      hcontrolWork).length =
      gates.length + 2 * (gates.map toffoliMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.length_append]
      rw [ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]
      cases gate <;> simp [controlledWithWorkGates] <;> omega

/-- A clean-work control lift contains no physical X leaf. -/
theorem controlledListWithWorkGates_xMultiplicity_sum
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    ((controlledListWithWorkGates control work gates hcontrol hwork
        hcontrolWork).map xMultiplicity).sum = 0 := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.map_append, List.sum_append]
      rw [ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]
      cases gate <;> simp [controlledWithWorkGates]

/-- The CNOT coordinate of a clean-work control lift is the source X
coordinate. -/
theorem controlledListWithWorkGates_cnotMultiplicity_sum
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    ((controlledListWithWorkGates control work gates hcontrol hwork
        hcontrolWork).map cnotMultiplicity).sum =
      (gates.map xMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.map_append, List.sum_append]
      rw [ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]
      cases gate <;> simp [controlledWithWorkGates]

/-- Exact Toffoli coordinate of a clean-work control lift: source X gates
become CNOT, source CNOT gates become one Toffoli, and source Toffoli gates
become three Toffoli gates. -/
theorem controlledListWithWorkGates_toffoliMultiplicity_sum
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    ((controlledListWithWorkGates control work gates hcontrol hwork
        hcontrolWork).map toffoliMultiplicity).sum =
      (gates.map cnotMultiplicity).sum +
        3 * (gates.map toffoliMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.map_append, List.sum_append]
      rw [ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]
      cases gate <;> simp [controlledWithWorkGates] <;> omega



/-- A list control lift maps the source list to its strict event expansions. -/
theorem map_event_controlledListWithWorkGates
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledListWithWorkGates control work gates hcontrol hwork
        hcontrolWork).map event = gates.flatMap controlledEventExpansion := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [controlledListWithWorkGates, List.map_append, List.flatMap_cons,
        map_event_controlledWithWorkGates]
      rw [ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))]

/-- Semantic action of a clean-work controlled gate list. -/
def controlledListWithWorkStep
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    Data -> Data :=
  stepList (controlledListWithWorkGates control work gates hcontrol hwork
    hcontrolWork)

/-- Direct realization proof for a clean-work controlled gate list. -/
theorem controlledListWithWorkWitness
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    UnitaryCircuit.Realizes encoding
      (programList
        (controlledListWithWorkGates control work gates hcontrol hwork
          hcontrolWork))
      (controlledListWithWorkStep control work gates hcontrol hwork
        hcontrolWork) :=
  witnessList (controlledListWithWorkGates control work gates hcontrol hwork
    hcontrolWork)

/-- If the extra control is false, the clean-work controlled gate list is a
no-op. -/
theorem controlledListWithWorkStep_eq_self_of_control_false
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolFalse : control.get x = false) :
    controlledListWithWorkStep control work gates hcontrol hwork
      hcontrolWork x = x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        stepList
          (controlledWithWorkGates control work gate
              (hcontrol gate (by simp)) (hwork gate (by simp))
              hcontrolWork ++
            controlledListWithWorkGates control work rest
              (fun next hnext => hcontrol next (by simp [hnext]))
              (fun next hnext => hwork next (by simp [hnext]))
              hcontrolWork) x = x
      rw [stepList_append]
      have hhead :
          stepList
              (controlledWithWorkGates control work gate
                (hcontrol gate (by simp)) (hwork gate (by simp))
                hcontrolWork) x = x := by
        simpa [controlledWithWorkStep] using
          controlledWithWorkStep_eq_self_of_control_false control work gate
            (hcontrol gate (by simp)) (hwork gate (by simp))
            hcontrolWork x hcontrolFalse
      rw [hhead]
      exact ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        x hcontrolFalse

/-- If the extra control is true and the work bit starts clean, the clean-work
controlled gate list acts like the original gate list. -/
theorem controlledListWithWorkStep_eq_stepList_of_control_true
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (x : Data)
    (hcontrolTrue : control.get x = true)
    (hworkClean : work.get x = false) :
    controlledListWithWorkStep control work gates hcontrol hwork
      hcontrolWork x = stepList gates x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        stepList
          (controlledWithWorkGates control work gate
              (hcontrol gate (by simp)) (hwork gate (by simp))
              hcontrolWork ++
            controlledListWithWorkGates control work rest
              (fun next hnext => hcontrol next (by simp [hnext]))
              (fun next hnext => hwork next (by simp [hnext]))
              hcontrolWork) x =
        stepList rest (gate.step x)
      rw [stepList_append]
      have hhead :
          stepList
              (controlledWithWorkGates control work gate
                (hcontrol gate (by simp)) (hwork gate (by simp))
                hcontrolWork) x = gate.step x := by
        simpa [controlledWithWorkStep] using
          controlledWithWorkStep_eq_step_of_control_true control work gate
            (hcontrol gate (by simp)) (hwork gate (by simp))
            hcontrolWork x hcontrolTrue hworkClean
      rw [hhead]
      have hcontrolNext : control.get (gate.step x) = true := by
        rw [step_get_of_bitDisjoint gate control (hcontrol gate (by simp)) x]
        exact hcontrolTrue
      have hworkNext : work.get (gate.step x) = false := by
        rw [step_get_of_bitDisjoint gate work (hwork gate (by simp)) x]
        exact hworkClean
      exact ih
        (fun next hnext => hcontrol next (by simp [hnext]))
        (fun next hnext => hwork next (by simp [hnext]))
        (gate.step x) hcontrolNext hworkNext

end GateSpec

end EncodedBit

end

end QuantumAlg

end
