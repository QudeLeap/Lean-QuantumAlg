/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Endpoint
public import QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Algorithm.Unitary.Endpoint
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete execution of a supplied owned quantum interface

The input context owns exactly the supplied physical layout. Equal-wire
placement changes only the dependent carrier, retaining the actual native
construction, event counts and depth. All supplied systems remain live.
-/

namespace QuantumAlg.UnitaryExecution.Owned
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {width : Nat}

/-- One supplied owned layout; every physical system is retained in the final output. -/
public def context (layout : QuantumLayout width) : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addOwnedLayout ⟨0⟩ layout (by decide)
    (by simp only [RuntimeCtx.runtimeCtx_empty_physicalIdx, List.disjoint_nil_right])

private theorem sameWires (layout : QuantumLayout width) :
    layout.wires = (context layout).quantumLayout.wires := by
  rw [RuntimeCtx.quantumLayout_wires]
  change layout.wires = layout.wires ++ []
  exact (List.append_nil _).symm

/-- The independent mathematical operator in the complete owned context. -/
public def target {layout : QuantumLayout width} (operator : UnitaryOperator layout.register) :
    UnitaryOperator (context layout).register :=
  UnitaryOperator.reindex
    (Execution.basisOfEqualWires layout (context layout).quantumLayout (sameWires layout)) operator

/-- Preserve the actual word when placing it in the equal-wire owned context. -/
public def program {layout : QuantumLayout width}
    (word : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles (context layout).quantumLayout :=
  Execution.unitaryOfEqualWires layout (context layout).quantumLayout (sameWires layout) word

/-- **Input.** An arbitrary normalized state on the supplied owned quantum layout.
**Output.** Every supplied system, transformed by the specified operator.
**Resource budget.** Independent event and depth limits; exactly the supplied live layout.
**Success.** Exact action on the full joint state, including any external reference.
**Source.** Complete-state unitary execution and equal-physical-wire placement. -/
public def problem {layout : QuantumLayout width} (operator : UnitaryOperator layout.register)
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat) :
    Problem (.quantum gates oracles) (context layout) (context layout) .unit :=
  UnitaryExecution.problem (target operator)
    { events := events
      resident := SpacePool.ofQuantumLayout layout
      auxiliary := SpacePool.ofQuantumLayout layout }
    { duration := fun _ => 1
      limit := limit
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- Complete output of the actual placed native construction. -/
public def algorithm {layout : QuantumLayout width} (word : UnitaryCircuit gates oracles layout) :
    Algorithm (.quantum gates oracles) (context layout) (context layout) .unit :=
  UnitaryExecution.algorithm (program word)

/-- Exact operator equality and native bounds certify the whole owned-interface execution. -/
public theorem main {layout : QuantumLayout width} (operator : UnitaryOperator layout.register)
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat)
    (word : UnitaryCircuit gates oracles layout) (same : word.matrix = operator)
    (cost : word.eventCost ≤ events)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ limit) :
    Algorithm.Solves (algorithm word) (problem operator events limit) := by
  apply UnitaryExecution.main
  · rw [program, Execution.unitaryOfEqualWires_matrix, same]
    rfl
  · rfl
  · rfl
  · exact cost
  · simp only [context, RuntimeCtx.residentSpace_addOwnedLayout,
      RuntimeCtx.residentSpace_empty, add_zero, le_refl]
  · simp only [context, RuntimeCtx.auxiliarySpace_addOwnedLayout,
      RuntimeCtx.auxiliarySpace_empty, add_zero, le_refl]
  · exact depth

end
end QuantumAlg.UnitaryExecution.Owned
