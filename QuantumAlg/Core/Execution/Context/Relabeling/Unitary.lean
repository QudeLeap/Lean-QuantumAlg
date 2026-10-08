/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Relabeling.Layout
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Native unitary instructions on injectively mapped systems

The existing physical relabeling constructor rewrites every native gate's
system addresses. Its logical reindexing uses the corresponding finite values
on those same mapped systems. The actual emitted native event list, cost and
evaluated depth remain unchanged.
-/

namespace QuantumAlg.Execution.ContextRelabeling

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  (ctx : RuntimeCtx .quantum) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
  (program : UnitaryCircuit gates oracles ctx.quantumLayout)

private def placement : QuantumLayout.Embedding (ctx.quantumLayout.relabel physical)
    (ctx.relabel keys physical).quantumLayout where
  position := (positions ctx keys physical).toEmbedding
  wire_eq := positions_wire ctx keys physical

private theorem placement_basis (value : (ctx.relabel keys physical).register.Index) :
    ((placement ctx keys physical).splitBasis value).1 =
      (basis ctx keys physical).symm value := by
  funext index
  apply Fin.ext
  have unchanged := basis_value ctx keys physical ((basis ctx keys physical).symm value) index
  rw [Equiv.apply_symm_apply] at unchanged
  exact (QuantumLayout.Embedding.embedding_splitBasis_selected_value
    (placement ctx keys physical) value index).trans unchanged.symm

/-- Move every actual native and query placement into the complete mapped context layout. -/
def unitaryProgram : UnitaryCircuit gates oracles (ctx.relabel keys physical).quantumLayout :=
  UnitaryCircuit.embed (placement ctx keys physical) (program.relabel physical)

/-- Every matrix entry follows the original finite values on the mapped actual wires. -/
theorem unitaryProgram_matrix (row column : (ctx.relabel keys physical).register.Index) :
    (unitaryProgram ctx keys physical program).matrix row column =
      program.matrix ((basis ctx keys physical).symm row)
        ((basis ctx keys physical).symm column) := by
  change (placement ctx keys physical).liftOperator (program.relabel physical).matrix
    row column = _
  rw [QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (placement ctx keys physical) (positions ctx keys physical).surjective,
    placement_basis, placement_basis, UnitaryCircuit.relabel_matrix]

/-- The entire emitted native event list retains its exact original order. -/
theorem unitaryProgram_trace (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryProgram ctx keys physical program).eventTrace operations services =
      program.eventTrace operations services :=
  UnitaryCircuit.relabel_eventTrace program physical operations services

/-- Actual physical placement leaves every native event count unchanged. -/
theorem unitaryProgram_cost (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (unitaryProgram ctx keys physical program).eventCost operations services =
      program.eventCost operations services :=
  UnitaryCircuit.relabel_eventCost program physical operations services

/-- Every native duration assignment gives exactly the original evaluated dependency depth. -/
theorem unitaryProgram_depth (operations : ClassicalOpModel) (services : ClassicalOracleModel)
    (duration : Resource.Event (.quantum gates oracles operations services) → Nat) :
    DepthExpr.depthEval duration
        ((unitaryProgram ctx keys physical program).eventDepth operations services) =
      DepthExpr.depthEval duration (program.eventDepth operations services) :=
  congrArg (DepthExpr.depthEval duration)
    (UnitaryCircuit.relabel_eventDepth program physical operations services)

/-- An arbitrary reference keeps every original joint operator entry under the same coordinates. -/
theorem unitaryProgram_joint_entry (Reference : Register)
    (row column : (ctx.relabel keys physical).register.Index)
    (referenceRow referenceColumn : Reference.Index) :
    (UnitaryOperator.prodTensor (unitaryProgram ctx keys physical program).matrix
      (1 : UnitaryOperator Reference)) (row, referenceRow) (column, referenceColumn) =
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
          ((basis ctx keys physical).symm row, referenceRow)
          ((basis ctx keys physical).symm column, referenceColumn) := by
  rw [UnitaryOperator.prodTensor_apply, UnitaryOperator.prodTensor_apply, unitaryProgram_matrix]

end

end QuantumAlg.Execution.ContextRelabeling
