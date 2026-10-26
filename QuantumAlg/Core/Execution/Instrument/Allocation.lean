/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum

public import QuantumAlg.Core.Execution.Instrument.Recorded
import all QuantumAlg.Core.Execution.Instrument.Recorded
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum

/-!
# Construct the exact retained instrument through the original lexical scopes

The dependent pair carries only the finite outcome type and the existing
RecordedInstrument. Actual workspace constructors wrap the specified child
instrument in the same order as the original classical allocator. No
arbitrary witness is chosen from an existence proposition. Every operator
reads the actual pushed Store and returned service state; all real paths
remain in the existing complete-record certificate.
-/

public section

namespace QuantumAlg.Execution

noncomputable section

open Execution ClassicalWorkspace

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- Only the outcome carrier is packaged; the execution certificate remains the existing type. -/
abbrev RecordedInstrument.Packed
    (code : Circuit (.quantum gates oracles operations services) ctx ctx true)
    (environment : (ExecutionModel.quantum gates oracles operations
      services).Environment) : Type 1 :=
  Σ Outcome : Type, Σ finite : Fintype Outcome,
    letI : Fintype Outcome := finite
    RecordedInstrument code Outcome environment

/-- A supplied actual certificate enters the dependent pair without selecting a new witness. -/
def RecordedInstrument.pack {Outcome : Type} [Fintype Outcome]
    {code : Circuit (.quantum gates oracles operations services) ctx ctx true}
    (actual : RecordedInstrument code Outcome environment) :
    RecordedInstrument.Packed code environment :=
  ⟨Outcome, inferInstance, actual⟩

/-- The same child certificate passes through its literal actual workspace constructor. -/
def packedWorkspace (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument.Packed code environment) :
    RecordedInstrument.Packed (Circuit.workspace
      (model := .quantum gates oracles operations services)
      ctx key shape fresh code) environment := by
  letI : Fintype actual.1 := actual.2.1
  exact ⟨actual.1, actual.2.1, actual.2.2.workspace key shape fresh⟩

/-- Workspace lifting keeps the literal full returned Store, hidden state and child Path. -/
private lemma packedWorkspace_record (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument.Packed code environment)
    (original : Store ctx × services.HiddenState) (outcome : actual.1) :
    letI : Fintype actual.1 := actual.2.1
    letI : Fintype (packedWorkspace key shape fresh actual).1 :=
      (packedWorkspace key shape fresh actual).2.1
    (packedWorkspace key shape fresh actual).2.2.record original outcome =
      sourceWorkspaceRecord key shape fresh actual.2.2.record original outcome := rfl

/-- The same local matrix reads the original actual pushed Store, with no quantum transport. -/
private lemma packedWorkspace_operator (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument.Packed code environment)
    (original : Store ctx × services.HiddenState) (outcome : actual.1) :
    letI : Fintype actual.1 := actual.2.1
    letI : Fintype (packedWorkspace key shape fresh actual).1 :=
      (packedWorkspace key shape fresh actual).2.1
    (packedWorkspace key shape fresh actual).2.2.operator original outcome =
      actual.2.2.operator (original.1.pushWorkspace key shape fresh, original.2) outcome := rfl

/-- Symbolic recursion constructs the supplied child through exactly the existing scopes. -/
def recordedWithCellsFrom {outer : RuntimeCtx .quantum}
    (transport : Transport outer ctx) (same : outer.quantumWires = ctx.quantumWires)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx .quantum} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
      outer.quantumWires = inner.quantumWires →
        Circuit (.quantum gates oracles operations services) inner inner true)
    (actual : ∀ {inner : RuntimeCtx .quantum} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires),
      RecordedInstrument.Packed (body cells distinct innerTransport separated innerSame)
        environment) :
    RecordedInstrument.Packed
      (withCellsWithQuantumWiresFrom transport same shapes body) environment := by
  induction shapes generalizing ctx with
  | nil => exact actual _ _ _ _ _
  | cons shape shapes inductionHypothesis =>
      dsimp only [withCellsWithQuantumWiresFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated innerSame
      exact packedWorkspace inner.canonicalFreshKey shape inner.canonicalFreshKey_fresh
        (actual _ _ _ _ _)

/-- Begin with the same original context, storage identity and complete ordered quantum wires. -/
def recordedWithCells (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx .quantum} (cells : Cells inner shapes), cells.Distinct →
      (innerTransport : Transport ctx inner) → cells.TransportSeparated innerTransport →
      ctx.quantumWires = inner.quantumWires →
        Circuit (.quantum gates oracles operations services) inner inner true)
    (actual : ∀ {inner : RuntimeCtx .quantum} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport ctx inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      RecordedInstrument.Packed (body cells distinct innerTransport separated innerSame)
        environment) :
    RecordedInstrument.Packed (withCellsWithQuantumWires
      (model := .quantum gates oracles operations services) ctx shapes body)
        environment :=
  recordedWithCellsFrom (Transport.id ctx) rfl shapes body actual

end

end QuantumAlg.Execution
