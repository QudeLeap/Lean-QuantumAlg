/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Accounting
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Quantum.Time
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Quantum.Resources
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Separate actual resources through the physical-bank-preserving table scope

The original five-array builder pays its native classical work once. Its
quantum event coordinates and quantum duration vanish by the original
instruction ledger. The actual allocation-free consumer retains its own
native quantum bounds on the same complete physical bank.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel}

variable [selectedModel : BitWord.Selected (.quantum gates oracles operations services)]
  {ctx : RuntimeCtx .quantum} {wordWidth window : Nat}
  (frame : Frame ctx wordWidth) (spec : ModulusSpec wordWidth) (row : Fin 34)
  (body : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
    ctx.quantumLayout.wires = inner.quantumLayout.wires →
    TableFrame inner wordWidth (2 ^ window) →
      Circuit (.quantum gates oracles operations services) inner inner false)

include gates oracles operations services selectedModel

/-- The same builder and actual consumer retain their independent native classical charges. -/
lemma Frame.withConstructedQuantumTables_classical_weight_le (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner wordWidth (2 ^ window)) (path : (body lift same table).Path),
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((body lift same table).resourcePool path) ≤ budget)
    (path : (frame.withConstructedQuantumTables spec row body).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.withConstructedQuantumTables spec row body).resourcePool path) ≤
        TableFrame.constructionBudget wordWidth window + budget := by
  unfold Frame.withConstructedQuantumTables withCellsWithQuantumWires
  apply withCellsWithQuantumWiresFrom_weightedCount_le
  intro inner cells distinct lift separated same selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := table.circuit_classical_weight_le
    (model := .quantum gates oracles operations services) spec selected.1
  have consumed := bodyBound lift (quantumLayout_wires_of_quantumWires same) table selected.2
  exact Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _ selected
    built (by simpa only [Circuit.resourcePool_embed] using consumed)

/-- Every native quantum coordinate comes from the actual consumer, with no classical conversion. -/
lemma Frame.withConstructedQuantumTables_count_le
    (focus : Resource.Event (.quantum gates oracles operations services))
    (nativeFree : ∀ coordinate, focus ≠ .classicalOperation coordinate) (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner wordWidth (2 ^ window)) (path : (body lift same table).Path),
      ResourcePool.count focus ((body lift same table).resourcePool path) ≤ budget)
    (path : (frame.withConstructedQuantumTables spec row body).Path) :
    ResourcePool.count focus
      ((frame.withConstructedQuantumTables spec row body).resourcePool path) ≤ budget := by
  unfold Frame.withConstructedQuantumTables withCellsWithQuantumWires
  have bounded := withCellsWithQuantumWiresFrom_property (Transport.id ctx) rfl
    (tableShapes wordWidth (2 ^ window))
    (fun cells distinct lift separated same =>
      let table := frame.tableFrame lift cells distinct separated row
      .seq (table.circuit spec)
        (.embed (ContextEmbedding.identity _)
          (body lift (quantumLayout_wires_of_quantumWires same) table)))
    (fun _ _ code => ∀ selected : code.Path,
      ResourcePool.count focus (code.resourcePool selected) ≤ budget)
    (fun _ _ _ _ _ _ available => available) (by
      intro inner cells distinct lift separated same selected
      let table := frame.tableFrame lift cells distinct separated row
      have built := QuantumAccounting.builder_count_zero focus nativeFree table spec selected.1
      have consumed := bodyBound lift (quantumLayout_wires_of_quantumWires same) table selected.2
      rw [Circuit.resourcePool_count_seq, built, Nat.zero_add, Circuit.resourcePool_embed]
      exact consumed)
  exact bounded path

/-- Actual classical construction leaves the consumer's native quantum depth allowance unchanged. -/
lemma Frame.withConstructedQuantumTables_quantumTime_le (budget : Nat)
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner wordWidth (2 ^ window)) (path : (body lift same table).Path),
      (body lift same table).depth Resource.Event.quantumDuration path ≤ budget)
    (path : (frame.withConstructedQuantumTables spec row body).Path) :
    (frame.withConstructedQuantumTables spec row body).depth
      Resource.Event.quantumDuration path ≤ budget := by
  unfold Frame.withConstructedQuantumTables withCellsWithQuantumWires
  apply withCellsWithQuantumWiresFrom_depth_le
  intro inner cells distinct lift separated same selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := QuantumAccounting.quantumTime_zero
    (table.circuit (model := .quantum gates oracles operations services) spec)
    (fun focus nativeFree => QuantumAccounting.builder_count_zero focus nativeFree table spec)
    selected.1
  change (table.circuit (model := (.quantum gates oracles operations services)) spec).depth
    Resource.Event.quantumDuration selected.1 + _ ≤ _
  rw [show (table.circuit (model := (.quantum gates oracles operations services)) spec).depth
    Resource.Event.quantumDuration selected.1 = 0 from built, Nat.zero_add]
  exact bodyBound lift (quantumLayout_wires_of_quantumWires same) table selected.2

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
