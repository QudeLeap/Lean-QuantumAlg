/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Success
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Restoration
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native Shor factoring from the original public inputs

One actual run prepares its bank, performs every original sampled quantum
round, restores the same bank and recovers the first accepted factor through
real finite classical instructions. Its complete Output, probability, state,
borrowed restoration and independent resources all refer to this same code.
-/

namespace QuantumAlg.Factoring.ShorStyle

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The original validity condition uses only the unique local input store. -/
public theorem problem_valid_iff {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed)
    (state : ExecutionState (Execution.Store pre) pre.register) :
    (problem model budget wellFormed).valid state ↔
      ∀ store, 0 < (state.block store).mass → store = inputStore := Iff.rfl

/-- The closed native implementation internally constructs every sample and arithmetic stage. -/
public def algorithm {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) : Algorithm .quantum pre (post model budget) (OutputShape N) where
  run := Canonical.NativeEndpoint.run (Canonical.Probability.Input.ofSemiprimeModel model)
    (Canonical.retryCount N budget)

private theorem actual_success {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) {Reference : Register}
    (input : Execution.Input pre Reference) :
    (problem model budget wellFormed).successLB.value ≤
      ((Canonical.NativeEndpoint.run (Canonical.Probability.Input.ofSemiprimeModel model)
        (Canonical.retryCount N budget)).relationalDistribution input).toOuterMeasure
          {pair | (problem model budget wellFormed).accepts pair.1 pair.2} := by
  have projection :
      ((Canonical.NativeEndpoint.run (Canonical.Probability.Input.ofSemiprimeModel model)
        (Canonical.retryCount N budget)).relationalDistribution input).toOuterMeasure
          {pair | (problem model budget wellFormed).accepts pair.1 pair.2} =
        ((Canonical.NativeEndpoint.run (Canonical.Probability.Input.ofSemiprimeModel model)
          (Canonical.retryCount N budget)).outputDistribution input).toOuterMeasure
            {output | Canonical.Probability.ReturnedDeclaredFactor model output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact Canonical.NativeEndpoint.output_success_probability_ge model budget wellFormed input

/-- The same complete native algorithm satisfies every obligation of the independent problem. -/
public theorem algorithm_solves {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    (algorithm model budget).Solves (problem model budget wellFormed) := by
  constructor
  · intro Reference input _valid
    simp only [Algorithm.relationalDistribution, algorithm]
    dsimp only [post]
    exact actual_success model budget wellFormed input
  · intro Reference input _valid requirement present
    have same : requirement =
        Canonical.NativeEndpoint.stateRequirement N (Canonical.retryCount N budget) :=
      List.mem_singleton.mp present
    subst requirement
    exact Canonical.NativeEndpoint.stateRequirement_holds _ _ input
  · intro Reference input _valid
    exact Canonical.NativeEndpoint.run_restoresBorrowed _ _ input
  · intro _Reference _input _valid path _supported
    exact Canonical.NativeEndpoint.code_pool_le _ _ path
  · intro _Reference _input _valid path _supported
    exact Canonical.NativeEndpoint.code_resident_le _ _ path
  · intro _Reference _input _valid path _supported
    exact Canonical.NativeEndpoint.code_auxiliary_le _ _ path
  · intro _Reference _input _valid path _supported
    exact Canonical.NativeEndpoint.code_unitDepth_le _ _ path

/-- Native Shor factoring retains the original distinct-prime and rational failure domain. -/
public theorem main {N p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hN : N = p * q) (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∃ candidate : Algorithm .quantum pre
      (post (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget) (OutputShape N),
      candidate.Solves
        (problem (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget wellFormed) :=
  ⟨algorithm (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget,
    algorithm_solves (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget wellFormed⟩

end

end QuantumAlg.Factoring.ShorStyle
