/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Instrument.Allocation.Read
import all QuantumAlg.Core.Execution.Instrument.Allocation.Read
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Read

/-!
# The specified retained operator acts through the original classical scopes

The same complete physical label and arbitrary reference pass through the
actual lexical classical allocations. Each supplied child is the existing
Packed certificate. The proof follows its tail-first construction and
retains its literal outcome, pushed Store and hidden state.
-/

namespace QuantumAlg.Execution

noncomputable section

open Execution ClassicalWorkspace
open Instrument

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- A complete physical basis label beside the same arbitrary reference value. -/
def scopedReferenceKet {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires) (label : physical.Basis)
    {Reference : Register} (reference : Reference.Index) :
    HilbertVector (ctx.register.prod Reference) :=
  (NormalizedVector.ket (R := ctx.register.prod Reference)
    (basisOfEqualWires physical ctx.quantumLayout same label, reference)).vec

/-- The literal pushed Store uses the same child operator and unchanged quantum bank. -/
lemma packedWorkspace_action {outer : RuntimeCtx .quantum}
    (transport : Transport outer ctx) (before : Store outer)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    {code : Circuit (.quantum gates oracles operations services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh) true}
    (actual : RecordedInstrument.Packed code environment)
    {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ) (Reference : Register)
    (reference : Reference.Index)
    (childAction : letI : Fintype actual.1 := actual.2.1
      ∀ (original : Store (ctx.addWorkspace key shape fresh) × services.HiddenState)
        (outcome : actual.1),
        (transport.underWorkspace key shape fresh).ReadsAs before original.1 →
        HilbertOperator.applyVec
          (referenceLift (Local := (ctx.addWorkspace key shape fresh).register)
            Reference (actual.2.2.operator original outcome))
          (scopedReferenceKet physical same initial (Reference := Reference) reference) =
            scalar • scopedReferenceKet physical same final (Reference := Reference) reference) :
    let chosen := packedWorkspace key shape fresh actual
    letI : Fintype chosen.1 := chosen.2.1
    ∀ (original : Store ctx × services.HiddenState) (outcome : chosen.1),
      transport.ReadsAs before original.1 →
      HilbertOperator.applyVec
        (referenceLift (Local := ctx.register) Reference (chosen.2.2.operator original outcome))
        (scopedReferenceKet physical same initial (Reference := Reference) reference) =
          scalar • scopedReferenceKet physical same final (Reference := Reference) reference := by
  let _ : Fintype actual.1 := actual.2.1
  dsimp only
  intro original outcome reads
  have operator := packedWorkspace_operator (ctx := ctx) (operations := operations)
    (services := services) (environment := environment) key shape fresh
    (code := code) actual original outcome
  exact (congrArg (fun matrix : HilbertOperator ctx.register =>
    HilbertOperator.applyVec (referenceLift (Local := ctx.register) Reference matrix)
      (scopedReferenceKet physical same initial (Reference := Reference) reference)) operator).trans
    (childAction (original.1.pushWorkspace key shape fresh, original.2) outcome
      (transport.workspaceTransport_readsAs_pushWorkspace key shape fresh reads))

/-- The same supplied child action passes through every actual tail-first allocation. -/
lemma recordedWithCellsFrom_action {outer : RuntimeCtx .quantum}
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
    (before : Store outer) {count : Nat} (physical : QuantumLayout count)
    (physicalSame : physical.wires = outer.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ) (Reference : Register)
    (reference : Reference.Index)
    (childAction : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport outer inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : outer.quantumWires = inner.quantumWires),
      let chosen := actual cells distinct innerTransport separated innerSame
      letI : Fintype chosen.1 := chosen.2.1
      ∀ (original : Store inner × services.HiddenState) (outcome : chosen.1),
        innerTransport.ReadsAs before original.1 →
        HilbertOperator.applyVec
          (referenceLift (Local := inner.register) Reference
            (chosen.2.2.operator original outcome))
          (scopedReferenceKet physical
            (physicalSame.trans (quantumLayout_wires_of_quantumWires innerSame))
            initial (Reference := Reference) reference) =
          scalar • scopedReferenceKet physical
            (physicalSame.trans (quantumLayout_wires_of_quantumWires innerSame))
            final (Reference := Reference) reference) :
    let chosen := recordedWithCellsFrom transport same shapes body actual
    letI : Fintype chosen.1 := chosen.2.1
    ∀ (original : Store ctx × services.HiddenState) (outcome : chosen.1),
      transport.ReadsAs before original.1 →
      HilbertOperator.applyVec
        (referenceLift (Local := ctx.register) Reference (chosen.2.2.operator original outcome))
        (scopedReferenceKet physical
          (physicalSame.trans (quantumLayout_wires_of_quantumWires same))
          initial (Reference := Reference) reference) =
        scalar • scopedReferenceKet physical
          (physicalSame.trans (quantumLayout_wires_of_quantumWires same))
          final (Reference := Reference) reference := by
  induction shapes generalizing ctx with
  | nil => exact childAction _ _ _ _ _
  | cons shape shapes inductionHypothesis =>
      dsimp only [recordedWithCellsFrom]
      apply inductionHypothesis
      intro inner cells distinct innerTransport separated innerSame
      apply packedWorkspace_action innerTransport before
      exact childAction _ _ _ _ _

/-- The actual outer Packed operator has the same label, coefficient and arbitrary reference. -/
lemma recordedWithCells_action (shapes : List CShape)
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
    (before : Store ctx) {count : Nat} (physical : QuantumLayout count)
    (same : physical.wires = ctx.quantumLayout.wires)
    (initial final : physical.Basis) (scalar : ℂ) (Reference : Register)
    (reference : Reference.Index)
    (childAction : ∀ {inner : RuntimeCtx .quantum} (cells : ClassicalWorkspace.Cells inner shapes)
      (distinct : cells.Distinct) (innerTransport : Transport ctx inner)
      (separated : cells.TransportSeparated innerTransport)
      (innerSame : ctx.quantumWires = inner.quantumWires),
      let chosen := actual cells distinct innerTransport separated innerSame
      letI : Fintype chosen.1 := chosen.2.1
      ∀ (original : Store inner × services.HiddenState) (outcome : chosen.1),
        innerTransport.ReadsAs before original.1 →
        HilbertOperator.applyVec
          (referenceLift (Local := inner.register) Reference
            (chosen.2.2.operator original outcome))
          (scopedReferenceKet physical
            (same.trans (quantumLayout_wires_of_quantumWires innerSame))
            initial (Reference := Reference) reference) =
          scalar • scopedReferenceKet physical
            (same.trans (quantumLayout_wires_of_quantumWires innerSame))
            final (Reference := Reference) reference) :
    let chosen := recordedWithCells shapes body actual
    letI : Fintype chosen.1 := chosen.2.1
    ∀ (hidden : services.HiddenState) (outcome : chosen.1),
      HilbertOperator.applyVec
        (referenceLift (Local := ctx.register) Reference
          (chosen.2.2.operator (before, hidden) outcome))
        (scopedReferenceKet physical same initial (Reference := Reference) reference) =
          scalar • scopedReferenceKet physical same final (Reference := Reference) reference := by
  dsimp only
  intro hidden outcome
  have action := recordedWithCellsFrom_action (ctx := ctx) (operations := operations)
    (services := services) (environment := environment) (Transport.id ctx) rfl shapes body actual
    before physical same initial final scalar Reference reference childAction
  exact action (before, hidden) outcome (Transport.workspaceTransport_readsAs_id before)

end

end QuantumAlg.Execution
