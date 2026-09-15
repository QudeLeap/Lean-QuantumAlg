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

variable (ctx : RuntimeCtx .quantum) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
  (program : UnitaryCircuit ctx.register) (placed : program.physical_idx = ctx.physicalIdx)

private def nativePlacement :
    PhysicalLayout.Relabeling program.physical_idx (ctx.relabel keys physical).physicalIdx where
  toFun := physical
  map_layout := by rw [placed, RuntimeCtx.relabel_physicalIdx]
  old_nodup := program.physical_idx_nodup
  new_nodup := (ctx.relabel keys physical).identitiesNodup

/-- Place the actual native gates and express their original operator in the mapped basis. -/
def unitaryProgram : UnitaryCircuit (ctx.relabel keys physical).register :=
  UnitaryCircuit.reindex (basis ctx keys physical)
    (program.relabel (nativePlacement ctx keys physical program placed))

/-- The emitted instruction occupies exactly the complete mapped physical context. -/
theorem unitaryProgram_physical :
    (unitaryProgram ctx keys physical program placed).physical_idx =
      (ctx.relabel keys physical).physicalIdx := rfl

/-- Every matrix entry follows the original finite values on the mapped actual wires. -/
theorem unitaryProgram_matrix (row column : (ctx.relabel keys physical).register.Index) :
    (unitaryProgram ctx keys physical program placed).matrix row column =
      program.matrix ((basis ctx keys physical).symm row)
        ((basis ctx keys physical).symm column) := by
  change (program.relabel (nativePlacement ctx keys physical program placed)).matrix
    ((basis ctx keys physical).symm row) ((basis ctx keys physical).symm column) = _
  exact congrArg (fun matrix : HilbertOperator ctx.register =>
    matrix ((basis ctx keys physical).symm row) ((basis ctx keys physical).symm column))
    (UnitaryCircuit.relabel_matrix program (nativePlacement ctx keys physical program placed))

/-- The entire emitted native event list retains its exact original order. -/
theorem unitaryProgram_trace :
    (unitaryProgram ctx keys physical program placed).eventTrace = program.eventTrace := by
  rw [unitaryProgram, UnitaryCircuit.reindex_eventTrace, UnitaryCircuit.relabel_eventTrace]

/-- Actual physical placement leaves every native event count unchanged. -/
theorem unitaryProgram_cost :
    (unitaryProgram ctx keys physical program placed).eventCost = program.eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, unitaryProgram_trace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- Every native duration assignment gives exactly the original evaluated dependency depth. -/
theorem unitaryProgram_depth (duration : Resource.Event .quantum → Nat) :
    (unitaryProgram ctx keys physical program placed).evaluatedEventDepth duration =
      program.evaluatedEventDepth duration := by
  change (program.relabel (nativePlacement ctx keys physical program placed)).evaluatedEventDepth
    duration = program.evaluatedEventDepth duration
  exact UnitaryCircuit.evaluatedEventDepth_relabel _ _ _

/-- An arbitrary reference keeps every original joint operator entry under the same coordinates. -/
theorem unitaryProgram_joint_entry (Reference : Register)
    (row column : (ctx.relabel keys physical).register.Index)
    (referenceRow referenceColumn : Reference.Index) :
    (UnitaryOperator.prodTensor (unitaryProgram ctx keys physical program placed).matrix
      (1 : UnitaryOperator Reference)) (row, referenceRow) (column, referenceColumn) =
        (UnitaryOperator.prodTensor program.matrix (1 : UnitaryOperator Reference))
          ((basis ctx keys physical).symm row, referenceRow)
          ((basis ctx keys physical).symm column, referenceColumn) := by
  rw [UnitaryOperator.prodTensor_apply, UnitaryOperator.prodTensor_apply, unitaryProgram_matrix]

end

end QuantumAlg.Execution.ContextRelabeling
