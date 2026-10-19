/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.AmplitudeAmplification.Endpoint
import all QuantumAlg.Primitives.AmplitudeAmplification.Endpoint
import all QuantumAlg.Primitives.AmplitudeAmplification.Endpoint.Execution

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Primitives.AmplitudeAmplification.Specification
public import QuantumAlg.Primitives.AmplitudeAmplification.Construction
public import QuantumAlg.Components.Oracle.ZeroReflection.Resources
public import QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Execution.Laws
import all QuantumAlg.Primitives.AmplitudeAmplification.Resources
import all QuantumAlg.Primitives.AmplitudeAmplification.Counts
import all QuantumAlg.Primitives.AmplitudeAmplification.Space
import all QuantumAlg.Primitives.AmplitudeAmplification.Restoration
import all QuantumAlg.Primitives.AmplitudeAmplification.Specification
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.SelectionAll
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Core.Execution.State.Promise
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed.Classical
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.Accounting.Weighted

/-!
# Complete native amplitude amplification at every source angle and iteration count

The endpoint executes actual preparation and source queries with an elementary
positive zero reflection. Its own final density proves the original exact
amplified state, with every prepared system retained and every external
reference restored. Resource formulas are checked against that same run.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The same fixed complete run satisfies every source witness and interpretation. -/
public lemma algorithm_solves (n k : Nat) :
    (algorithm n k).Solves (problem n k) := complete_correct n k

/-- No additional state or angle premise restricts the original mathematical source model. -/
public lemma problem_valid {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n) (k : Nat)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem n k).valid (environment M) M state := rfl

/-- The elementary gate count comes from the single actual complete execution. -/
public lemma algorithm_gateCount (n : Nat)
    (k : Nat) (path : (algorithm n k).run.code.Path) :
    ResourcePool.weightedCount (fun event => match event with
      | .gate _ => 1 | _ => 0) ((algorithm n k).run.code.resourcePool path) =
        k * ZeroReflection.elementaryGateCount n :=
  code_gateCount n k path

/-- Ordinary source preparation occurs initially and once in each actual iterate. -/
public lemma algorithm_preparationCount (n : Nat)
    (k : Nat) (path : (algorithm n k).run.code.Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model
        (AmplitudeAmplificationSource.model n true false))
      (.oracle .preparation)
      ((algorithm n k).run.code.resourcePool path) = k + 1 :=
  code_preparationCount n k path

/-- Every actual iterate contains precisely one ordinary inverse-source query. -/
public lemma algorithm_inversePreparationCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model
        (AmplitudeAmplificationSource.model n true false))
      (.oracle .inversePreparation)
      ((algorithm n k).run.code.resourcePool path) = k :=
  code_inversePreparationCount n k path

/-- The actual distinguishing good-reflection query occurs once per iterate. -/
public lemma algorithm_goodReflectionCount (n : Nat) (k : Nat)
    (path : (algorithm n k).run.code.Path) :
    ResourcePool.count
      (model := .quantum AlgorithmGate.model
        (AmplitudeAmplificationSource.model n true false))
      (.oracle .goodReflection)
      ((algorithm n k).run.code.resourcePool path) = k :=
  code_goodReflectionCount n k path

end

end QuantumAlg.AmplitudeAmplification
