/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Toffoli.Refinement
import all QuantumAlg.Components.Gates.Toffoli.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Refinement.Depth
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Native
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.Depth.Expr

/-!
# Actual dependency depth after Toffoli expansion

The fifteen-gate replacement occupies the same physical subsystem. Its depth
replaces a source Toffoli duration by fifteen, retaining unit duration for all
other native gates and granted queries. Parallel disjoint branches remain parallel.
-/

namespace QuantumAlg.Gate.Toffoli
noncomputable section

private def expandedDuration (oracles : OracleModel) :
    Resource.Event (.quantum AlgorithmGate.model oracles) → Nat
  | .gate .toffoli => 15
  | _ => 1

private lemma nativeExpansion_depth (oracles : OracleModel) {count : Nat}
    {ambient : QuantumLayout count}
    (application : GateModel.Application AlgorithmGate.model ambient) :
    (nativeExpansion oracles application).circuit.evaluatedEventDepth (fun _ => 1) =
      expandedDuration oracles (.gate application.coordinate) := by
  rcases application with ⟨⟨token, placement⟩, embedding⟩
  cases token with
  | toffoli =>
      change DepthExpr.depthEval (fun _ => 1)
        (UnitaryCircuit.placeAt _ _ _ _ (circuit oracles)).eventDepth = 15
      rw [UnitaryCircuit.placeAt_eventDepth]
      exact toffoliExpansion_depth oracles
  | cnot => rfl
  | singleQubit operator => rfl

private lemma depthEval_constant {U : Type} (expression : DepthExpr U) (duration : Nat) :
    expression.depthEval (fun _ => duration) =
      duration * expression.depthEval (fun _ => 1) := by
  induction expression with
  | id => simp
  | atom unit => simp
  | seq left right leftIH rightIH => simp [leftIH, rightIH, Nat.mul_add]
  | tensor left right leftIH rightIH =>
      simp only [DepthExpr.depthEval_tensor, leftIH, rightIH]
      exact (mul_max duration (left.depthEval fun _ => 1)
        (right.depthEval fun _ => 1)).symm
  | inverse body ih => simpa using ih
  | controlled controls body ih => simpa using ih
  | iterate repetitions body ih => simp [ih, Nat.mul_left_comm]
  | indexedProduct label steps start step startIH stepIH =>
      simp [startIH, stepIH, Nat.mul_add, Finset.mul_sum]

/-- Expanding the actual construction multiplies its unit dependency depth by at most fifteen. -/
lemma toffoliExpansion_depth_le {oracles : OracleModel} {count : Nat}
    {ambient : QuantumLayout count} (source : UnitaryCircuit AlgorithmGate.model oracles ambient) :
    (expand source).evaluatedEventDepth (fun _ => 1) ≤
      15 * source.evaluatedEventDepth (fun _ => 1) := by
  have exactDepth := UnitaryCircuit.refine_evaluatedEventDepth source
    (expansionInstructions oracles) (expandedDuration oracles) (fun _ => 1)
    (nativeExpansion_depth oracles) (by intro width layout application; rfl)
  change (source.refine (expansionInstructions oracles)).evaluatedEventDepth (fun _ => 1) ≤ _
  rw [exactDepth]
  have bound : ∀ event, expandedDuration oracles event ≤ 15 := by
    intro event
    cases event with
    | gate coordinate => cases coordinate <;> simp [expandedDuration]
    | classicalOperation impossible => cases impossible
    | classicalQuery impossible => cases impossible
    | oracle coordinate => simp [expandedDuration]
    | preparation dimension => simp [expandedDuration]
    | measurement dimension => simp [expandedDuration]
  exact (DepthExpr.depthEval_mono bound source.eventDepth).trans_eq
    (depthEval_constant source.eventDepth 15)

end
end QuantumAlg.Gate.Toffoli
