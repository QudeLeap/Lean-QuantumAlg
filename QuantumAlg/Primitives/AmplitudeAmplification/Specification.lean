/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.AmplitudeAmplification.Model
public import QuantumAlg.Primitives.AmplitudeAmplification.Context
public import QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Model
import all QuantumAlg.Primitives.AmplitudeAmplification.Context
import all QuantumAlg.Primitives.AmplitudeAmplification.Program.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Workspace
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Accounting.Space

/-!
# Independent complete amplitude-amplification specification

The source model's angle remains any real number, and the iteration count
any natural number. The exact state target is the original plane formula,
not a projection of the tested program. Bounds are explicit parameter formulas.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

open QuantumAlg.ZeroReflection.Workspace

/-- One zero preparation per physical qubit, followed by independent source-iterate counts. -/
public def eventBudget (n : Nat) (k : Nat) :
    ResourcePool (model n) :=
  totalQubits n k • ResourcePool.singleton (model := model n) (.preparation (2 : ℕ+)) +
    Native.unitaryEventPool n k

/-- Every prepared source or helper system remains live and owned; no classical cells exist. -/
public def spaceBudget (n k : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then totalQubits n k else 0

/-- Charged initial basis preparation and source preparation precede the actual k iterates. -/
public def depthBudget (n k : Nat) : Nat := 2 + k * (3 + ZeroReflection.elementaryGateCount n)

/-- The original exact source state and retained zero helper in the actual output coordinates. -/
public def targetState {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    DensityOperator ((post n k).quantumLayout.selectedRegister Finset.univ) :=
  (DensityOperator.ofPure ((M.amplifiedState k).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0))).reindex
    ((preparedBasisEquiv n k).symm.trans (post n k).quantumLayout.allSelectedBasisEquiv)

lemma targetState_normalized {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (targetState M k).IsNormalized := by
  change (targetState M k).mass = 1
  rw [targetState, DensityOperator.reindex_mass]
  exact DensityOperator.ofPure_normalized ((M.amplifiedState k).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0))

/-- Observe all actual source and helper systems as one joint exact state. -/
public def stateRequirement {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    StateRequirement pre (post n k) :=
  .marginal Finset.univ .unit fun _ _ => .mixed (targetState M k) (targetState_normalized M k)

end

end QuantumAlg.AmplitudeAmplification
