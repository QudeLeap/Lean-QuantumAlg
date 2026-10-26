/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Transport

public import QuantumAlg.Core.Execution.Instrument.Allocation
import all QuantumAlg.Core.Execution.Instrument.Allocation
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport

/-!
# Caller reads of the specified retained instrument through actual scopes

The existing constructor keeps the chosen child record at every lexical
scope. Its actual push and pop preserve each structurally transported
caller read. Induction follows the same symbolic allocation list and
retains the full returned Store, hidden state and original child Path.
-/

namespace QuantumAlg.Execution

noncomputable section

open Execution ClassicalWorkspace

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The literal actual push and pop transport a protected child read to its parent. -/
lemma packedWorkspace_read (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument.Packed code environment) {observedShape : CShape}
    (observed : CInputRef ctx observedShape)
    (childRead : letI : Fintype actual.1 := actual.2.1
      ∀ original outcome,
        (actual.2.2.record original outcome).1.1.read (observed.underWorkspace key shape fresh) =
          original.1.read (observed.underWorkspace key shape fresh)) :
    letI : Fintype (packedWorkspace key shape fresh actual).1 :=
      (packedWorkspace key shape fresh actual).2.1
    ∀ original outcome,
      ((packedWorkspace key shape fresh actual).2.2.record original outcome).1.1.read observed =
        original.1.read observed := by
  let _ : Fintype actual.1 := actual.2.1
  intro original outcome
  change (Store.popWorkspace key shape fresh
    (actual.2.2.record (original.1.pushWorkspace key shape fresh, original.2) outcome).1.1).read
      observed = original.1.read observed
  exact (Store.read_popWorkspace_underWorkspace key shape fresh _ observed).trans
    ((childRead (original.1.pushWorkspace key shape fresh, original.2) outcome).trans
      (Store.read_pushWorkspace_underWorkspace original.1 key shape fresh observed))

/-- Exact constructor recursion preserves the original transported read through all real scopes. -/
lemma recordedWithCellsFrom_read {outer : RuntimeCtx .quantum}
    (transport : Transport outer ctx) (same : outer.quantumWires = ctx.quantumWires)
    (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes),
      cells.Distinct →
      (innerTransport : Transport outer inner) → cells.TransportSeparated innerTransport →
      outer.quantumWires = inner.quantumWires →
        Circuit (.quantum gates oracles operations services) inner inner true)
    (actual : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires),
      RecordedInstrument.Packed (body cells distinct innerTransport separated innerSame)
        environment)
    {observedShape : CShape} (observed : CInputRef outer observedShape)
    (childRead : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires),
      let chosen := actual cells distinct innerTransport separated innerSame
      letI : Fintype chosen.1 := chosen.2.1
      ∀ original outcome,
        (chosen.2.2.record original outcome).1.1.read (innerTransport.liftInput observed) =
          original.1.read (innerTransport.liftInput observed)) :
    let chosen := recordedWithCellsFrom transport same shapes body actual
    letI : Fintype chosen.1 := chosen.2.1
    ∀ original outcome,
      (chosen.2.2.record original outcome).1.1.read (transport.liftInput observed) =
        original.1.read (transport.liftInput observed) := by
  induction shapes generalizing ctx with
  | nil => exact childRead _ _ _ _ _
  | cons shape shapes inductionHypothesis =>
      dsimp only [recordedWithCellsFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated innerSame
      apply packedWorkspace_read
      rw [← Transport.liftInput_underWorkspace]
      exact childRead _ _ _ _ _

/-- The same original read is retained after all actual classical scopes have been released. -/
lemma recordedWithCells_read (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes),
      cells.Distinct →
      (innerTransport : Transport ctx inner) → cells.TransportSeparated innerTransport →
      ctx.quantumWires = inner.quantumWires →
        Circuit (.quantum gates oracles operations services) inner inner true)
    (actual : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport ctx inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      RecordedInstrument.Packed (body cells distinct innerTransport separated innerSame)
        environment)
    {observedShape : CShape} (observed : CInputRef ctx observedShape)
    (childRead : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport ctx inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      let chosen := actual cells distinct innerTransport separated innerSame
      letI : Fintype chosen.1 := chosen.2.1
      ∀ original outcome,
        (chosen.2.2.record original outcome).1.1.read (innerTransport.liftInput observed) =
          original.1.read (innerTransport.liftInput observed)) :
    let chosen := recordedWithCells shapes body actual
    letI : Fintype chosen.1 := chosen.2.1
    ∀ original outcome,
      (chosen.2.2.record original outcome).1.1.read observed = original.1.read observed := by
  unfold recordedWithCells
  simpa only [Transport.liftInput_id] using
    recordedWithCellsFrom_read (ctx := ctx) (operations := operations) (services := services)
      (environment := environment) (Transport.id ctx) rfl shapes body actual observed childRead

end

end QuantumAlg.Execution
