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
def eventBudget {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    ResourcePool (model M) :=
  totalQubits n k • ResourcePool.singleton (model := model M) (.preparation (2 : ℕ+)) +
    Native.unitaryEventPool M.preparation M.good k

/-- Every prepared source or helper system remains live and owned; no classical cells exist. -/
def spaceBudget (n k : Nat) : SpacePool .quantum
  | .classicalBits => 0
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then totalQubits n k else 0

/-- Charged initial basis preparation and source preparation precede the actual k iterates. -/
def depthBudget (n k : Nat) : Nat := 2 + k * (3 + ZeroReflection.elementaryGateCount n)

/-- The original exact source state and retained zero helper in the actual output coordinates. -/
def targetState {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    DensityOperator ((post n k).quantumLayout.selectedRegister Finset.univ) :=
  (DensityOperator.ofPure ((M.amplifiedState k).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0))).reindex
    ((preparedBasisEquiv n k).symm.trans (post n k).quantumLayout.allSelectedBasisEquiv)

theorem targetState_normalized {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    (targetState M k).IsNormalized := by
  change (targetState M k).mass = 1
  rw [targetState, DensityOperator.reindex_mass]
  exact DensityOperator.ofPure_normalized ((M.amplifiedState k).tensor
    (NormalizedVector.ket (R := Qubits (helperWidth n k)) 0))

/-- Observe all actual source and helper systems as one joint exact state. -/
def stateRequirement {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    StateRequirement pre (post n k) :=
  .marginal Finset.univ .unit fun _ _ => .mixed (targetState M k) (targetState_normalized M k)

/-- Complete native source-query amplitude amplification.

**Input.** The original normalized good/bad source plane, measurement-free
preparation unitary A and its exact prepared-state decomposition, with any
real angle and any natural iteration count k. Runtime input is empty and all
normalized external-reference states are admitted.
**Output.** The source has bad/good amplitudes cos((2k+1)θ) and sin((2k+1)θ).
Every selected helper is retained in its original prepared zero state; the
complete Output keeps the entire joint source/helper register and returns unit.
**Resource budget.** One zero preparation per actual source/helper qubit, k+1 ordinary A
queries, k inverse-A queries and k distinguishing good-reflection queries.
Each known positive zero reflection uses the independently counted elementary
gates, for k times that count in total. There are n+h owned quantum systems,
where h is zero for k=0 or n≤3 and otherwise one; no classical bits exist.
Unit-event depth is at most 2+k(3+D(n)), where D is the elementary reflection count.
**Success.** Probability one with the exact joint output-state requirement and
mandatory restoration of the complete external reference, at every angle and k.
**Source.** Measurement-free amplification and the exact good/bad-plane rotation
[dW19, qcnotes.tex:2914-2964]. The known reflection is synthesized with exact
phase and a restored helper; no controlled access to A is assumed.
-/
public def problem {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat) :
    Problem (.quantum AlgorithmGate.model
      (AmplitudeAmplificationSource.model M.preparation M.good true false))
      pre (post n k) .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := [stateRequirement M k]
  resources :=
    { events := eventBudget M k
      resident := spaceBudget n k
      auxiliary := spaceBudget n k }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget n k
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.AmplitudeAmplification
