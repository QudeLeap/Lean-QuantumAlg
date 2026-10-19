/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.ZReset.Circuit
public import QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Resources
import all QuantumAlg.Primitives.ZReset.Circuit
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit

/-!
# Exact native resources of measurement and stored-value correction

Each path contains one Z measurement followed by the complete native expansion
of its selected exact correction. A zero correction may be empty. The original
physical systems, classical result cell and auxiliary roles stay resident.
The correction's dependency tree retains any internal parallelism.

Resource and depth envelopes take independent bounds from the caller. Their
correctness premises bound every supplied correction; no mathematical shift
label is admitted as a native event and no budget is extracted from the reset
run being checked. The underlying measurement and unitary state operations
are [dW19, qcnotes.tex:5409] and [dW19, qcnotes.tex:5405].
-/

namespace QuantumAlg.ZReset

noncomputable section

variable {services : ClassicalOracleModel}

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {ctx : RuntimeCtx .quantum}
variable (wire : Fin ctx.systemCount)
  (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
  (realizations : QuditShift.Realizations gates oracles ctx.quantumLayout wire)

private instance resetResourceDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- The actual finite value recorded by the classical branch read. -/
@[expose, implicit_reducible]
public def readOutcome {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations
  operations).Path) :
    Fin (ctx.quantumLayout.wire wire).dimension := path.2.1.toFin

/-- A path records the measurement and a matching read of its actual stored result. -/
@[expose, implicit_reducible]
public def pathFor {allowAllocation : Bool}
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).Path := (outcome, ⟨.finite
      outcome, ()⟩)

/-- Consistent measurement and read records select that same finite value. -/
public lemma zReset_readOutcome_pathFor {allowAllocation : Bool}
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    readOutcome (allowAllocation := allowAllocation) (services := services) (operations :=
        operations) wire output realizations
      (pathFor (allowAllocation := allowAllocation) (services := services) wire output realizations
          outcome) = outcome := rfl

/-- The ordered trace includes every actual correction operation after its Z measurement. -/
public lemma zReset_eventTrace {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations
  operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).eventTrace path =
      Resource.Event.measurement (model := .quantum gates oracles operations services)
        (ctx.quantumLayout.wire wire).dimension ::
        (realizations (-(readOutcome (allowAllocation := allowAllocation) (services := services)
            (operations := operations)
          wire output realizations path))).circuit.eventTrace operations services := by
  simpa only [circuit, Circuit.zEvent, readOutcome] using
    QuditShift.resetCircuit_eventTrace (allowAllocation := allowAllocation) (operations :=
        operations) wire output realizations path

/-- The exact ledger counts the same complete native expansion. -/
public lemma zReset_resourcePool {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations
  operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).resourcePool path =
      ResourcePool.ofList (Resource.Event.measurement (model := .quantum gates oracles operations
        services)
        (ctx.quantumLayout.wire wire).dimension ::
        (realizations (-(readOutcome (allowAllocation := allowAllocation) (services := services)
            (operations := operations)
          wire output realizations path))).circuit.eventTrace operations services) := by
  simpa only [circuit, Circuit.zEvent, readOutcome] using
    QuditShift.resetCircuit_pool (allowAllocation := allowAllocation) (operations := operations)
        wire output realizations path

/-- Actual length is one measurement plus the selected correction's complete length. -/
public lemma zReset_eventTrace_length {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    ((circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).eventTrace path).length =
      1 + ((realizations (-(readOutcome (allowAllocation := allowAllocation) (services := services)
          (operations := operations)
        wire output realizations path))).circuit.eventTrace operations services).length :=
  (congrArg List.length (zReset_eventTrace (allowAllocation := allowAllocation) (operations :=
      operations)
    wire output realizations path)).trans
    (List.length_cons.trans (Nat.add_comm _ _))

/-- Measurement and correction both retain the original complete live context. -/
public lemma zReset_visitedContexts {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
  realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).visitedContexts path =
      [ctx, ctx] :=
  QuditShift.resetCircuit_visited (allowAllocation := allowAllocation) (operations := operations)
      wire output realizations path

/-- Resident peak includes every original physical system and classical cell. -/
public lemma zReset_peakResidentSpace {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).peakResidentSpace path =
      ctx.residentSpace :=
  QuditShift.resetCircuit_resident (allowAllocation := allowAllocation) (operations := operations)
      wire output realizations path

/-- Auxiliary peak uses the unchanged roles of those same existing entries. -/
public lemma zReset_peakAuxiliarySpace {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).peakAuxiliarySpace path =
      ctx.auxiliarySpace :=
  QuditShift.resetCircuit_auxiliary (allowAllocation := allowAllocation) (operations := operations)
      wire output realizations path

/-- The actual native dependency is Z measurement followed by the entire correction. -/
public lemma zReset_eventDepth {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations
  operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).eventDepth path =
      .seq (.atom (Resource.Event.measurement (model := .quantum gates oracles operations services)
        (ctx.quantumLayout.wire wire).dimension))
        ((realizations (-(readOutcome (allowAllocation := allowAllocation) (services := services)
            (operations := operations)
          wire output realizations path))).circuit.eventDepth operations services) := by
  simpa only [circuit, Circuit.zEvent, readOutcome] using
    QuditShift.resetCircuit_eventDepth (allowAllocation := allowAllocation) (operations :=
        operations) wire output realizations path

/-- Durations add along the real measurement-to-correction dependency. -/
public lemma zReset_depth {allowAllocation : Bool}
    (duration : Resource.Event (.quantum gates oracles operations services)
  → Nat)
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).depth duration path =
      duration (Resource.Event.measurement (model := .quantum gates oracles operations services)
        (ctx.quantumLayout.wire wire).dimension) +
        DepthExpr.depthEval duration ((realizations (-(readOutcome
            (allowAllocation := allowAllocation) (services := services)
          (operations := operations)
          wire output realizations path))).circuit.eventDepth operations services) := by
  simpa only [circuit, Circuit.zEvent, readOutcome] using
    QuditShift.resetCircuit_depth (allowAllocation := allowAllocation) (operations := operations)
        wire output realizations duration path

/-- Unit depth charges the selected implementation instead of a fictional unit shift. -/
public lemma zReset_unitDepth {allowAllocation : Bool}
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations
  operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).depth (fun _ => 1) path =
      1 + DepthExpr.depthEval (fun _ => 1)
        ((realizations (-(readOutcome (allowAllocation := allowAllocation) (services := services)
            (operations := operations)
          wire output realizations path))).circuit.eventDepth operations services) :=
  QuditShift.resetCircuit_unitDepth (allowAllocation := allowAllocation) (operations := operations)
      wire output realizations path

/-- An independently supplied correction budget plus the required Z event. -/
public def eventEnvelope (dimension : ℕ+)
    (correctionBudget : ResourcePool (.quantum gates oracles operations services)) :
    ResourcePool (.quantum gates oracles operations services) :=
  ResourcePool.singleton
    (Resource.Event.measurement (model := .quantum gates oracles operations services) dimension) +
      correctionBudget

/-- A uniform independent correction bound covers every actual selected path. -/
public lemma zReset_resourcePool_le_envelope {allowAllocation : Bool}
    (correctionBudget : ResourcePool (.quantum gates oracles operations services))
    (bounded : ∀ amount,
      ResourcePool.ofList ((realizations amount).circuit.eventTrace operations services) ≤
        correctionBudget)
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).resourcePool path ≤
      eventEnvelope (ctx.quantumLayout.wire wire).dimension correctionBudget := by
  rw [zReset_resourcePool (allowAllocation := allowAllocation), ResourcePool.ofList_cons,
      eventEnvelope]
  exact add_le_add le_rfl
    (bounded (-(readOutcome (allowAllocation := allowAllocation) (services := services) (operations
        := operations) wire output
      realizations path)))

/-- An independent correction depth bound retains the preceding measurement duration. -/
public def depthEnvelope (dimension : ℕ+)
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat)
    (correctionDepth : Nat) : Nat :=
  duration (Resource.Event.measurement (model := .quantum gates oracles operations services)
    dimension) +
    correctionDepth

/-- Each real correction fits the independently supplied dependency-depth bound. -/
public lemma zReset_depth_le_envelope {allowAllocation : Bool}
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat) (correctionDepth
      : Nat)
    (bounded : ∀ amount,
      DepthExpr.depthEval duration ((realizations amount).circuit.eventDepth operations services) ≤
        correctionDepth)
    (path : (circuit (allowAllocation := allowAllocation) (services := services) wire output
        realizations operations).Path) :
    (circuit (allowAllocation := allowAllocation) (services := services) wire output realizations
        operations).depth duration path ≤
      depthEnvelope (ctx.quantumLayout.wire wire).dimension duration correctionDepth :=
  Nat.add_le_add_left
    (bounded (-(readOutcome (allowAllocation := allowAllocation) (services := services) (operations
        := operations) wire output
      realizations path))) _

end

end QuantumAlg.ZReset
