/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Unitary.Owned
public import QuantumAlg.Core.Algorithm.Unitary.Approximate.Endpoint
public import QuantumAlg.Core.Base.Gate.OperatorNorm.Reindex
import all QuantumAlg.Core.Algorithm.Unitary.Owned
import all QuantumAlg.Core.Algorithm.Unitary.Approximate.Endpoint
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Base.Gate.OperatorNorm.Reindex

/-!
# Approximate execution on a supplied owned layout

Equal-wire placement preserves the system operator-norm bound and the same
actual construction's events and depth. The independent input and output own
exactly the supplied layout, and retain arbitrary external correlations.
-/

namespace QuantumAlg.UnitaryExecution.ApproximateOwned
noncomputable section

variable {gates : GateModel} {oracles : OracleModel} {width : Nat}

/-- **Input.** Any normalized joint state on the supplied owned layout and external reference.
**Output.** Every supplied system after a system unitary within the independent error bound.
**Resource budget.** Independent events and time; exactly the supplied live layout.
**Success.** Probability one and the complete reference-aware unitary neighborhood.
**Source.** Full-phase operator approximation and equal-physical-wire transport. -/
public def problem {layout : QuantumLayout width}
    (operator : oracles.Interpretation → UnitaryOperator layout.register)
    (error : ℝ) (nonnegative : 0 ≤ error)
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat) :
    Problem (.quantum gates oracles) (Owned.context layout) (Owned.context layout) .unit :=
  Approximate.problem (fun environment => Owned.target (operator environment)) error nonnegative
    { events := events
      resident := SpacePool.ofQuantumLayout layout
      auxiliary := SpacePool.ofQuantumLayout layout }
    limit

/-- Native approximation and independent bounds certify the complete owned execution. -/
public theorem main {layout : QuantumLayout width}
    (operator : oracles.Interpretation → UnitaryOperator layout.register)
    (error : ℝ) (nonnegative : 0 ≤ error)
    (events : ResourcePool (.quantum gates oracles)) (limit : Nat)
    (word : UnitaryCircuit gates oracles layout)
    (close : ∀ environment, HilbertOperator.opNorm
      ((word.matrix environment : HilbertOperator layout.register) -
        (operator environment : HilbertOperator layout.register)) ≤ error)
    (cost : word.eventCost ≤ events)
    (depth : word.evaluatedEventDepth (fun _ => 1) ≤ limit) :
    Algorithm.Solves (Owned.algorithm word) (problem operator error nonnegative events limit) := by
  apply Approximate.main
  · intro environment
    rw [Owned.program, Execution.unitaryOfEqualWires_matrix]
    exact (HilbertOperator.opNorm_reindex_sub _ _ _).le.trans (close environment)
  · rfl
  · rfl
  · exact cost
  · simp only [Owned.context, RuntimeCtx.residentSpace_addOwnedLayout,
      RuntimeCtx.residentSpace_empty, add_zero, le_refl]
  · simp only [Owned.context, RuntimeCtx.auxiliarySpace_addOwnedLayout,
      RuntimeCtx.auxiliarySpace_empty, add_zero, le_refl]
  · exact (DepthExpr.depthEval_mono Resource.Event.quantumDuration_le_one _).trans depth

end
end QuantumAlg.UnitaryExecution.ApproximateOwned
