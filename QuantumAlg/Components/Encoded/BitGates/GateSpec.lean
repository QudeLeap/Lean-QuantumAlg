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

/-- The addressed primitive retains the exact source wire arguments and disjointness. -/
def primitive : GateSpec encoding → QubitPrimitive encoding.width
  | .x target => .x target.wire
  | .cnot control target different => .cnot control.wire target.wire different
  | .toffoli first second target distinct firstTarget secondTarget =>
      .toffoli first.wire second.wire target.wire distinct firstTarget secondTarget

/-- The actual default-model coordinate in the independently selected oracle environment. -/
def event (oracles : OracleModel) (gate : GateSpec encoding) :
    Resource.Event (.quantum AlgorithmGate.model oracles) :=
  (primitive gate).event oracles

/-- Semantic relabeling keeps the physical primitive and its model-owned event unchanged. -/
@[simp] lemma event_relabel (oracles : OracleModel) {Other : Type}
    (layout : Other ≃ Data) (gate : GateSpec encoding) :
    event oracles (relabel layout gate) = event oracles gate := by
  cases gate <;> rfl

/-- Relabeling the semantic data preserves the ordered native event trace. -/
lemma map_event_relabel (oracles : OracleModel) {Other : Type} (layout : Other ≃ Data)
    (gates : List (GateSpec encoding)) :
    (gates.map (relabel layout)).map (event oracles) = gates.map (event oracles) := by
  induction gates with
  | nil => rfl
  | cons gate gates ih =>
      change event oracles (relabel layout gate) ::
          ((gates.map (relabel layout)).map (event oracles)) =
        event oracles gate :: gates.map (event oracles)
      rw [event_relabel, ih]

/-- Right-associated dependency depth of an ordered trace in the selected model. -/
def depthOfEvents {model : ExecutionModel} : List (Resource.Event model) →
    DepthExpr (Resource.Event model)
  | [] => .id
  | emitted :: rest => .seq (.atom emitted) (depthOfEvents rest)

/-- Compile one semantic bit operation on its actual physical interface. -/
def program (gate : GateSpec encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  (primitive gate).circuit layout oracles

/-- The actual native instruction emits precisely its declaration-owned event. -/
@[simp] lemma program_eventTrace (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    (gate.program layout oracles).eventTrace = [event oracles gate] :=
  QubitPrimitive.primitiveCircuit_eventTrace (primitive gate) layout oracles

/-- Native multiplicity is computed from the same instruction that executes. -/
@[simp] lemma program_eventCost (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    (gate.program layout oracles).eventCost = ResourcePool.singleton (event oracles gate) :=
  QubitPrimitive.primitiveCircuit_eventCost (primitive gate) layout oracles

/-- An addressed source primitive executes as one native dependency step. -/
@[simp] lemma program_eventDepth (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    (gate.program layout oracles).eventDepth = .atom (event oracles gate) :=
  QubitPrimitive.primitiveCircuit_eventDepth (primitive gate) layout oracles

/-- Native bit instructions perform no query, even when an oracle environment is available. -/
lemma program_oracle_count_zero (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel)
    (query : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (gate.program layout oracles).eventCost = 0 := by
  rw [program_eventCost]
  apply ResourcePool.count_singleton_of_ne
  cases gate <;> simp [event, primitive, QubitPrimitive.event, QubitPrimitive.nativeToken]

/-- The actual primitive contributes one native event, independently of its wire positions. -/
lemma program_eventCost_card (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    (gate.program layout oracles).eventCost.card = 1 := by
  rw [program_eventCost]
  simp [ResourcePool.singleton]

/-- Every coordinate distinct from this actual instruction receives zero charge. -/
lemma program_event_count_zero_of_ne (gate : GateSpec encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    (different : focus ≠ event oracles gate) :
    ResourcePool.count focus (gate.program layout oracles).eventCost = 0 := by
  rw [program_eventCost]
  exact ResourcePool.count_singleton_of_ne different 1

/-- Semantic action of one encoded-bit operation. -/
def step : GateSpec encoding → Data → Data
  | x target => target.flip
  | cnot control target _hct => cnotStep control target
  | toffoli controlA controlB target _hab _ha _hb =>
      toffoliStep controlA controlB target

/-- Semantic relabeling conjugates the primitive action by the supplied
layout equivalence. -/
lemma step_relabel {Other : Type} (layout : Other ≃ Data)
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
lemma step_step (gate : GateSpec encoding) (x : Data) :
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
lemma step_preserves_of_targetFlipPreserves {α : Type}
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
lemma step_flip_comm_of_bitDisjoint
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
lemma step_get_of_bitDisjoint
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

variable (layout : QubitLayout encoding.width) (oracles : OracleModel)

/-- One actual placed native operation realizes its original semantic update. -/
lemma realizes (gate : GateSpec encoding) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (gate.program layout oracles) environment gate.step := by
  cases gate with
  | x target => exact x_realizes target environment
  | cnot control target different => exact cnot_realizes control target different environment
  | toffoli first second target distinct firstTarget secondTarget =>
      exact toffoli_realizes first second target distinct firstTarget secondTarget environment

/-- Execute the literal list on the complete supplied physical layout. -/
def programList (layout : QubitLayout encoding.width) (oracles : OracleModel) :
    List (GateSpec encoding) → UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum
  | [] => UnitaryCircuit.identity AlgorithmGate.model oracles layout.toQuantum
  | gate :: rest => (gate.program layout oracles).seq (programList layout oracles rest)

/-- The event trace comes from the actual native instructions, in list order. -/
@[simp] lemma programList_eventTrace (gates : List (GateSpec encoding)) :
    (programList layout oracles gates).eventTrace = gates.map (event oracles) := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.seq_eventTrace, program_eventTrace, ih]
      rfl

/-- The actual event pool retains literal multiplicity in the selected model. -/
@[simp] lemma programList_eventCost (gates : List (GateSpec encoding)) :
    (programList layout oracles gates).eventCost =
      ResourcePool.ofList (gates.map (event oracles)) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, programList_eventTrace]

/-- The actual dependency tree is the right-associated source event schedule. -/
@[simp] lemma programList_eventDepth (gates : List (GateSpec encoding)) :
    (programList layout oracles gates).eventDepth =
      depthOfEvents (gates.map (event oracles)) := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      change DepthExpr.seq (gate.program layout oracles).eventDepth
        (programList layout oracles rest).eventDepth = DepthExpr.seq _ _
      rw [program_eventDepth, ih]

/-- A list of native instructions makes no quantum oracle query. -/
lemma programList_oracle_count_zero (gates : List (GateSpec encoding))
    (query : oracles.Coordinate) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles) (.oracle query)
      (programList layout oracles gates).eventCost = 0 := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        program_oracle_count_zero, ih, Nat.zero_add]

/-- The literal native list has exactly one executed event per source operation. -/
lemma programList_eventCost_card (gates : List (GateSpec encoding)) :
    (programList layout oracles gates).eventCost.card = gates.length := by
  rw [programList_eventCost]
  simp [ResourcePool.ofList]

/-- With unit durations, the actual sequential depth is exactly the list length. -/
@[simp] lemma programList_evaluatedEventDepth_unit (gates : List (GateSpec encoding)) :
    (programList layout oracles gates).evaluatedEventDepth (fun _ => 1) = gates.length := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      rw [programList, UnitaryCircuit.evaluatedEventDepth_seq, ih]
      have head : (gate.program layout oracles).evaluatedEventDepth (fun _ => 1) = 1 := by
        rw [UnitaryCircuit.evaluatedEventDepth, program_eventDepth]
        rfl
      rw [head, List.length_cons]
      omega

/-- Indicator of an actual selected-model event emitted by one native source operation. -/
def eventMultiplicity (oracles : OracleModel)
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    (gate : GateSpec encoding) : Nat :=
  if event oracles gate = focus then 1 else 0

/-- Equal events have equal indicators in the same declared environment. -/
lemma eventMultiplicity_eq_of_event_eq
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    {left right : GateSpec encoding} (same : event oracles left = event oracles right) :
    eventMultiplicity oracles focus left = eventMultiplicity oracles focus right := by
  simp [eventMultiplicity, same]

/-- Equal literal traces preserve every coordinate count. -/
lemma sum_eventMultiplicity_eq_of_events_eq
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    {Left Right : Type} {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)} {right : List (GateSpec rightEncoding)}
    (same : left.map (event oracles) = right.map (event oracles)) :
    (left.map (eventMultiplicity oracles focus)).sum =
      (right.map (eventMultiplicity oracles focus)).sum := by
  have first : left.map (eventMultiplicity oracles focus) =
      (left.map (event oracles)).map (fun emitted => if emitted = focus then 1 else 0) := by
    simp [eventMultiplicity, List.map_map, Function.comp_def]
  have second : right.map (eventMultiplicity oracles focus) =
      (right.map (event oracles)).map (fun emitted => if emitted = focus then 1 else 0) := by
    simp [eventMultiplicity, List.map_map, Function.comp_def]
  rw [first, second, same]

/-- Coordinate multiplicity follows from the same native list that is executed. -/
lemma programList_event_count_eq_sum_eventMultiplicity
    (focus : Resource.Event (.quantum AlgorithmGate.model oracles))
    (gates : List (GateSpec encoding)) :
    ResourcePool.count focus (programList layout oracles gates).eventCost =
      (gates.map (eventMultiplicity oracles focus)).sum := by
  rw [programList_eventCost, ResourcePool.count_ofList]
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.map_cons, List.sum_cons, List.count_cons]
      rw [ih]
      simp [eventMultiplicity, Nat.add_comm]

/-- A source X instruction is charged to the default single-qubit coordinate. -/
def xMultiplicity : GateSpec encoding → Nat
  | .x _ => 1
  | _ => 0

/-- Indicator of a source CNOT instruction. -/
def cnotMultiplicity : GateSpec encoding → Nat
  | .cnot _ _ _ => 1
  | _ => 0

/-- Indicator of a source Toffoli instruction. -/
def toffoliMultiplicity : GateSpec encoding → Nat
  | .toffoli _ _ _ _ _ _ => 1
  | _ => 0

private lemma eventMultiplicity_singleQubit :
    (eventMultiplicity oracles (.gate .singleQubit) : GateSpec encoding → Nat) =
      xMultiplicity := by
  funext gate
  cases gate <;> rfl

private lemma eventMultiplicity_cnot :
    (eventMultiplicity oracles (.gate .cnot) : GateSpec encoding → Nat) =
      cnotMultiplicity := by
  funext gate
  cases gate <;> rfl

private lemma eventMultiplicity_toffoli :
    (eventMultiplicity oracles (.gate .toffoli) : GateSpec encoding → Nat) =
      toffoliMultiplicity := by
  funext gate
  cases gate <;> rfl

/-- Equal native traces retain the source X multiplicity. -/
lemma sum_xMultiplicity_eq_of_events_eq
    {Left Right : Type} {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)} {right : List (GateSpec rightEncoding)}
    (same : left.map (event oracles) = right.map (event oracles)) :
    (left.map xMultiplicity).sum = (right.map xMultiplicity).sum := by
  have counts := sum_eventMultiplicity_eq_of_events_eq oracles (.gate .singleQubit) same
  simpa only [eventMultiplicity_singleQubit] using counts

/-- Equal native traces retain the source CNOT multiplicity. -/
lemma sum_cnotMultiplicity_eq_of_events_eq
    {Left Right : Type} {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)} {right : List (GateSpec rightEncoding)}
    (same : left.map (event oracles) = right.map (event oracles)) :
    (left.map cnotMultiplicity).sum = (right.map cnotMultiplicity).sum := by
  have counts := sum_eventMultiplicity_eq_of_events_eq oracles (.gate .cnot) same
  simpa only [eventMultiplicity_cnot] using counts

/-- Equal native traces retain the source TOFFOLI multiplicity. -/
lemma sum_toffoliMultiplicity_eq_of_events_eq
    {Left Right : Type} {leftEncoding : BinaryLabelEncoding Left}
    {rightEncoding : BinaryLabelEncoding Right}
    {left : List (GateSpec leftEncoding)} {right : List (GateSpec rightEncoding)}
    (same : left.map (event oracles) = right.map (event oracles)) :
    (left.map toffoliMultiplicity).sum = (right.map toffoliMultiplicity).sum := by
  have counts := sum_eventMultiplicity_eq_of_events_eq oracles (.gate .toffoli) same
  simpa only [eventMultiplicity_toffoli] using counts

@[simp] lemma xMultiplicity_x (target : EncodedBit encoding) :
    xMultiplicity (.x target) = 1 := rfl

@[simp] lemma xMultiplicity_cnot (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    xMultiplicity (.cnot control target hne) = 0 := rfl

@[simp] lemma xMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    xMultiplicity (.toffoli controlA controlB target hab ha hb) = 0 := rfl

@[simp] lemma cnotMultiplicity_x (target : EncodedBit encoding) :
    cnotMultiplicity (.x target) = 0 := rfl

@[simp] lemma cnotMultiplicity_cnot
    (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    cnotMultiplicity (.cnot control target hne) = 1 := rfl

@[simp] lemma cnotMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    cnotMultiplicity (.toffoli controlA controlB target hab ha hb) = 0 := rfl

@[simp] lemma toffoliMultiplicity_x (target : EncodedBit encoding) :
    toffoliMultiplicity (.x target) = 0 := rfl

@[simp] lemma toffoliMultiplicity_cnot
    (control target : EncodedBit encoding)
    (hne : control.wire ≠ target.wire) :
    toffoliMultiplicity (.cnot control target hne) = 0 := rfl

@[simp] lemma toffoliMultiplicity_toffoli
    (controlA controlB target : EncodedBit encoding)
    (hab : controlA.wire ≠ controlB.wire)
    (ha : controlA.wire ≠ target.wire)
    (hb : controlB.wire ≠ target.wire) :
    toffoliMultiplicity (.toffoli controlA controlB target hab ha hb) = 1 := rfl

/-- Every encoded-bit gate is exactly one X, CNOT, or Toffoli leaf, so the
physical list length is the sum of those three strict coordinates. -/
lemma length_eq_multiplicity_sums (gates : List (GateSpec encoding)) :
    gates.length =
      (gates.map xMultiplicity).sum +
        (gates.map cnotMultiplicity).sum +
        (gates.map toffoliMultiplicity).sum := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      cases gate <;> simp [ih] <;> omega

/-- The actual singleQubit coordinate counts precisely its source instructions. -/
lemma programList_x_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .singleQubit) (programList layout oracles gates).eventCost =
      (gates.map xMultiplicity).sum := by
  rw [programList_event_count_eq_sum_eventMultiplicity, eventMultiplicity_singleQubit]

/-- The actual cnot coordinate counts precisely its source instructions. -/
lemma programList_cnot_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .cnot) (programList layout oracles gates).eventCost =
      (gates.map cnotMultiplicity).sum := by
  rw [programList_event_count_eq_sum_eventMultiplicity, eventMultiplicity_cnot]

/-- The actual toffoli coordinate counts precisely its source instructions. -/
lemma programList_toffoli_count_eq_sum (gates : List (GateSpec encoding)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .toffoli) (programList layout oracles gates).eventCost =
      (gates.map toffoliMultiplicity).sum := by
  rw [programList_event_count_eq_sum_eventMultiplicity, eventMultiplicity_toffoli]

/-- Count the three actual default native coordinates of a supplied physical circuit. -/
def primitiveEventCount {count : Nat} {physical : QuantumLayout count}
    {oracles : OracleModel} (circuit : UnitaryCircuit AlgorithmGate.model oracles physical) : Nat :=
  ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .singleQubit) circuit.eventCost +
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .cnot) circuit.eventCost +
    ResourcePool.count (model := .quantum AlgorithmGate.model oracles)
      (.gate .toffoli) circuit.eventCost

/-- The source list emits exactly one of the three native coordinates per instruction. -/
@[simp] lemma primitiveEventCount_programList (gates : List (GateSpec encoding)) :
    primitiveEventCount (programList layout oracles gates) = gates.length := by
  rw [primitiveEventCount, programList_x_count_eq_sum, programList_cnot_count_eq_sum,
    programList_toffoli_count_eq_sum]
  exact (length_eq_multiplicity_sums gates).symm

/-- Equal source traces give equal actual native resource pools. -/
lemma programList_eventCost_eq_of_events_eq (left right : List (GateSpec encoding))
    (same : left.map (event oracles) = right.map (event oracles)) :
    (programList layout oracles left).eventCost = (programList layout oracles right).eventCost := by
  rw [programList_eventCost, programList_eventCost, same]

/-- Equal source traces give equal actual dependency paths. -/
lemma programList_eventDepth_eq_of_events_eq (left right : List (GateSpec encoding))
    (same : left.map (event oracles) = right.map (event oracles)) :
    (programList layout oracles left).eventDepth =
      (programList layout oracles right).eventDepth := by
  rw [programList_eventDepth, programList_eventDepth, same]

/-- Semantic action of a list of encoded-bit operations, in list execution
order. -/
def stepList : List (GateSpec encoding) → Data → Data
  | [] => id
  | gate :: rest => fun x => stepList rest (gate.step x)

/-- Relabeling every primitive conjugates the complete list fold by the same
semantic layout equivalence. -/
lemma stepList_relabel {Other : Type} (layout : Other ≃ Data) :
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
lemma stepList_preserves_of_targetFlipPreserves {α : Type}
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
lemma stepList_get_of_bitDisjoint
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
lemma stepList_flip_comm_of_bitDisjoint
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
lemma stepList_append (first second : List (GateSpec encoding)) (x : Data) :
    stepList (first ++ second) x = stepList second (stepList first x) := by
  induction first generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- Reversing a gate list gives a right inverse for its semantic step. -/
lemma stepList_reverse_stepList
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
lemma stepList_eq_foldl (gates : List (GateSpec encoding)) (x : Data) :
    stepList gates x = gates.foldl (fun y gate => gate.step y) x := by
  induction gates generalizing x with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [stepList, ih]

/-- A list of encoded-bit operations realizes its folded semantic action. -/
lemma realizesList (gates : List (GateSpec encoding)) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles gates) environment (stepList gates) := by
  induction gates with
  | nil =>
      simpa [programList, stepList] using
        UnitaryCircuit.Realizes.identityAt AlgorithmGate.model oracles encoding layout environment
  | cons gate rest ih =>
      simpa [programList, stepList] using
        UnitaryCircuit.Realizes.seq
          (firstStep := gate.step) (secondStep := stepList rest)
          (realizes layout oracles gate environment) ih

/-- A gate list realizes any step pointwise equal to its folded semantic
action. -/
lemma realizesList_congrStep (gates : List (GateSpec encoding))
    {step : Data -> Data}
    (hstep : ∀ x, stepList gates x = step x) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles gates) environment step where
  apply_encoded_ket := by
    intro x
    rw [(realizesList layout oracles gates environment).apply_encoded_ket x]
    rw [hstep x]

/-- Proof that the actual compiled list realizes its folded semantic step. -/
lemma witnessList (gates : List (GateSpec encoding)) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles gates) environment (stepList gates) :=
  realizesList layout oracles gates environment

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
lemma controlledWithWorkGates_length_le_three
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledWithWorkGates control work gate hcontrol hwork
      hcontrolWork).length ≤ 3 := by
  cases gate <;> simp [controlledWithWorkGates]

/-- Adding a clean external control and work bit preserves disjointness from
an unrelated observed bit. -/
lemma controlledWithWorkGates_bitDisjoint
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
def controlledEventExpansion (oracles : OracleModel) : GateSpec encoding →
    List (Resource.Event (.quantum AlgorithmGate.model oracles))
  | .x _ => [.gate .cnot]
  | .cnot _ _ _ => [.gate .toffoli]
  | .toffoli _ _ _ _ _ _ =>
      [.gate .toffoli, .gate .toffoli,
        .gate .toffoli]

/-- The controlled gate list exposes exactly the source gate's strict event
expansion, independently of wire addresses and proof fields. -/
lemma map_event_controlledWithWorkGates
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledWithWorkGates control work gate hcontrol hwork
        hcontrolWork).map (event oracles) = controlledEventExpansion oracles gate := by
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
lemma controlledWithWorkWitness
    (control work : EncodedBit encoding) (gate : GateSpec encoding)
    (hcontrol : bitDisjoint control gate)
    (hwork : bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles
        (controlledWithWorkGates control work gate hcontrol hwork hcontrolWork)) environment
      (controlledWithWorkStep control work gate hcontrol hwork hcontrolWork) :=
  witnessList layout oracles (controlledWithWorkGates control work gate hcontrol hwork
    hcontrolWork) environment

/-- If the extra control is false, the clean-work controlled gate is a no-op. -/
lemma controlledWithWorkStep_eq_self_of_control_false
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
lemma controlledWithWorkStep_eq_step_of_control_true
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
lemma controlledListWithWorkGates_bitDisjoint
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
lemma controlledListWithWorkGates_length_le_three_mul
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
lemma controlledListWithWorkGates_length_eq
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
lemma controlledListWithWorkGates_xMultiplicity_sum
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
lemma controlledListWithWorkGates_cnotMultiplicity_sum
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
lemma controlledListWithWorkGates_toffoliMultiplicity_sum
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
lemma map_event_controlledListWithWorkGates
    (control work : EncodedBit encoding)
    (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates → bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates → bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) :
    (controlledListWithWorkGates control work gates hcontrol hwork
        hcontrolWork).map (event oracles) = gates.flatMap (controlledEventExpansion oracles) := by
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
lemma controlledListWithWorkWitness
    (control work : EncodedBit encoding) (gates : List (GateSpec encoding))
    (hcontrol : ∀ gate, gate ∈ gates -> bitDisjoint control gate)
    (hwork : ∀ gate, gate ∈ gates -> bitDisjoint work gate)
    (hcontrolWork : control.wire ≠ work.wire) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes (layout := layout) encoding
      (programList layout oracles
        (controlledListWithWorkGates control work gates hcontrol hwork
          hcontrolWork)) environment
      (controlledListWithWorkStep control work gates hcontrol hwork
        hcontrolWork) :=
  witnessList layout oracles (controlledListWithWorkGates control work gates hcontrol hwork
    hcontrolWork) environment

/-- If the extra control is false, the clean-work controlled gate list is a
no-op. -/
lemma controlledListWithWorkStep_eq_self_of_control_false
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
lemma controlledListWithWorkStep_eq_stepList_of_control_true
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
