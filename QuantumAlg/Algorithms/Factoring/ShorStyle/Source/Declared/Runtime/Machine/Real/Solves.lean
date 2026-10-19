/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Protocol
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

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget

open Execution

noncomputable section

/-- The same actual machine satisfies original factoring success and every complete obligation. -/
lemma countAlgorithm_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    (count : Nat) (η : Real)
    (positive : 0 < η)
    (calibrated : ENNReal.ofReal (1 - η) ≤
      1 - (ENNReal.ofReal (sourceFailureBudget N).value) ^ count) :
    (countAlgorithm base noQuantum N input count).Solves
      (countProblem base noQuantum N input count η positive) := by
  constructor
  · intro actual model Reference original valid _admitted
    have same := environment_eq_of_quantum input actual valid
    subst actual
    change ENNReal.ofReal (1 - η) ≤
      ((run base noQuantum N input
        count).relationalDistribution (environment input) original).toOuterMeasure
          {pair | Probability.ReturnedDeclaredFactor model pair.2}
    have projection :
        ((run base noQuantum N input
          count).relationalDistribution (environment input) original).toOuterMeasure
            {pair | Probability.ReturnedDeclaredFactor model pair.2} =
        ((run base noQuantum N input
          count).outputDistribution (environment input) original).toOuterMeasure
            {value | Probability.ReturnedDeclaredFactor model value} := by
      simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
        PMF.toOuterMeasure_map_apply]
      rfl
    rw [projection]
    exact calibrated.trans (output_success_ge_power base noQuantum model count original)
  · intro actual _model Reference original valid _admitted requirement present
    have actual_eq := environment_eq_of_quantum input actual valid
    subst actual
    have same : requirement = stateRequirement base noQuantum N count :=
      List.mem_singleton.mp present
    subst requirement
    exact stateRequirement_holds base noQuantum N input
      count original
  · intro actual _model Reference original _valid _admitted
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_of_noBorrowedQuantum
      (code base noQuantum N input count) actual
      (Initialized.base_noBorrowedQuantum base noQuantum) reference state
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_pool_le base noQuantum N input
      count path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_resident_le base noQuantum N input
      count path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_auxiliary_le base noQuantum N input
      count path
  · intro _actual _model _Reference _original _valid _admitted path _supported
    exact code_depth_le base noQuantum N input
      count Resource.Event.quantumDuration path

/-- The directly selected real-target execution satisfies the full independent contract. -/
lemma shorRealTarget_machine_solves (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N)
    (η : Real) (positive : 0 < η) :
    (algorithm base noQuantum N input η).Solves
      (problem base noQuantum N input η positive) := by
  apply countAlgorithm_solves base noQuantum N input (repetitionCount N η) η positive
  rw [ENNReal.ofReal_sub _ positive.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left
    (repetition_failure_le input η positive) 1

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget
