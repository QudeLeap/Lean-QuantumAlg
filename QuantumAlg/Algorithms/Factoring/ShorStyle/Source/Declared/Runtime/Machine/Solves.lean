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
lemma shorDeclared_machine_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    (algorithm base noQuantum N input budget).Solves
      (problem base noQuantum N input budget wellFormed) := by
  constructor
  · intro actual model Reference original valid _admitted
    have same := environment_eq_of_quantum input actual valid
    subst actual
    change FailureBudget.successThreshold budget ≤
      ((run base noQuantum N input
        (retryCount N budget)).relationalDistribution (environment input) original).toOuterMeasure
          {pair | Probability.ReturnedDeclaredFactor model pair.2}
    have projection :
        ((run base noQuantum N input
          (retryCount N budget)).relationalDistribution (environment input) original).toOuterMeasure
            {pair | Probability.ReturnedDeclaredFactor model pair.2} =
        ((run base noQuantum N input
          (retryCount N budget)).outputDistribution (environment input) original).toOuterMeasure
            {value | Probability.ReturnedDeclaredFactor model value} := by
      simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
        PMF.toOuterMeasure_map_apply]
      rfl
    rw [projection]
    exact output_success_probability_ge base noQuantum model budget wellFormed original
  · intro actual _model Reference original valid _admitted requirement present
    have actual_eq := environment_eq_of_quantum input actual valid
    subst actual
    have same : requirement = stateRequirement base noQuantum N (retryCount N budget) :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N input
      (retryCount N budget) original
  · intro actual _model Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code base noQuantum N input (retryCount N budget)) actual
      (Initialized.base_noBorrowedQuantum base noQuantum) reference state
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_pool_le base noQuantum N input
      (retryCount N budget) path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_resident_le base noQuantum N input
      (retryCount N budget) path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_auxiliary_le base noQuantum N input
      (retryCount N budget) path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_depth_le base noQuantum N input
      (retryCount N budget) Resource.Event.quantumDuration path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
