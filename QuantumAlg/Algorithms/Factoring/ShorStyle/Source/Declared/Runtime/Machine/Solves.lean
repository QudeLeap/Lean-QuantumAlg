/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Protocol
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Solves
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix

/-!
# Original success and all resources of the same complete declared Shor machine

All seven obligations use the original initialized finite circuit, its actual
joint input/output law, every live reference fiber and every real path. The
success proof reuses the accepted original source law. No source probability,
prepared bank, success latch or private resource certificate is requested
from the caller.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

/-- The same actual machine satisfies original factoring success and every complete obligation. -/
theorem shorDeclared_machine_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    (algorithm base noQuantum model budget).Solves
      (problem base noQuantum model budget wellFormed duration unitQueries) := by
  constructor
  · intro Reference original _valid _admitted
    change FailureBudget.successThreshold budget ≤
      ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)
        (retryCount N budget)).relationalDistribution original).toOuterMeasure
          {pair | Probability.ReturnedDeclaredFactor model pair.2}
    have projection :
        ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)
          (retryCount N budget)).relationalDistribution original).toOuterMeasure
            {pair | Probability.ReturnedDeclaredFactor model pair.2} =
        ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)
          (retryCount N budget)).outputDistribution original).toOuterMeasure
            {value | Probability.ReturnedDeclaredFactor model value} := by
      simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
        PMF.toOuterMeasure_map_apply]
      rfl
    rw [projection]
    exact output_success_probability_ge base noQuantum model budget wellFormed original
  · intro Reference original _valid _admitted requirement present
    have same : requirement = stateRequirement base noQuantum N (retryCount N budget) :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N (Probability.Input.ofSemiprimeModel model)
      (retryCount N budget) original
  · intro Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code base noQuantum N (Probability.Input.ofSemiprimeModel model) (retryCount N budget))
      (Initialized.base_noBorrowedQuantum base noQuantum) reference state
  · intro _Reference _original _valid _admitted path _supported
    exact code_pool_le base noQuantum N (Probability.Input.ofSemiprimeModel model)
      (retryCount N budget) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_resident_le base noQuantum N (Probability.Input.ofSemiprimeModel model)
      (retryCount N budget) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_auxiliary_le base noQuantum N (Probability.Input.ofSemiprimeModel model)
      (retryCount N budget) path
  · intro _Reference _original _valid _admitted path _supported
    exact code_depth_le base noQuantum N (Probability.Input.ofSemiprimeModel model)
      (retryCount N budget) duration path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
