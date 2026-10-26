/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Scope.Quantum.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Resources.Events
import all QuantumAlg.Core.Base.Accounting.OracleWeight

/-!
# Complete finite native allowance through the actual quantum table scope

The original allocating five-array builder precedes the same physical-bank
consumer. Both independent full event pools are added. Classical scope entry
and release add no event and do not remove any actual builder instruction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

/-- The full original builder and actual consumer retain their independent native event pools. -/
lemma Frame.withConstructedQuantumTables_pool_le
    {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
    {services : ClassicalOracleModel}
    [BitWord.Selected (.quantum gates oracles operations services)]
    {ctx : RuntimeCtx .quantum} {wordWidth window : Nat}
    (frame : Frame ctx wordWidth) (spec : ModulusSpec wordWidth) (row : Fin 34)
    (body : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      TableFrame inner wordWidth (2 ^ window) →
        Circuit (.quantum gates oracles operations services) inner inner false)
    (budget : ResourcePool (.quantum gates oracles operations services))
    (bodyBound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (table : TableFrame inner wordWidth (2 ^ window)) (path : (body lift same table).Path),
      (body lift same table).resourcePool path ≤ budget)
    (path : (frame.withConstructedQuantumTables spec row body).Path) :
    (frame.withConstructedQuantumTables spec row body).resourcePool path ≤
      TableFrame.envelope (.quantum gates oracles operations services) window spec + budget := by
  classical
  apply ResourcePool.le_iff_count.mpr
  intro focus
  let weight : Resource.Event (.quantum gates oracles operations services) → Nat :=
    fun event => if event = focus then 1 else 0
  have indicator (pool : ResourcePool (.quantum gates oracles operations services)) :
      ResourcePool.weightedCount weight pool = ResourcePool.count focus pool :=
    ResourcePool.weightedCount_eq_count_of_indicator weight focus (fun _ => rfl) pool
  rw [← indicator]
  unfold Frame.withConstructedQuantumTables withCellsWithQuantumWires
  apply withCellsWithQuantumWiresFrom_weightedCount_le
  intro inner cells distinct lift separated same selected
  let table := frame.tableFrame lift cells distinct separated row
  have built := table.circuit_pool_le (model := .quantum gates oracles operations services)
    spec selected.1
  have consumed := bodyBound lift (quantumLayout_wires_of_quantumWires same) table selected.2
  rw [indicator]
  apply ResourcePool.le_iff_count.mp ?_ focus
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add built consumed

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
