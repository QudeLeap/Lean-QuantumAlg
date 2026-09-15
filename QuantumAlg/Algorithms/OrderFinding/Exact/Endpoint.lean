/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Specification
public import QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.OrderFinding.Exact.Mathematics
import all QuantumAlg.Algorithms.OrderFinding.Exact.Specification
import all QuantumAlg.Algorithms.OrderFinding.Exact.Execution
import all QuantumAlg.Algorithms.OrderFinding.Exact.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Exact.Restoration
import all QuantumAlg.Algorithms.OrderFinding.Exact.Resources
import all QuantumAlg.Algorithms.OrderFinding.Exact.Space
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Measure.Distribution

/-!
# Complete native exact-dyadic order finding

The original query circuit prepares and measures its actual physical systems.
Its stored bits drive the existing shift-and-increment decoder and complete
Output reads the resulting unsigned word. The single execution's probabilities,
borrowed correlations, event counts and storage peaks satisfy the independent
problem without an additional execution or accounting premise.
-/

namespace QuantumAlg.OrderFinding

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The public input domain is exactly the original positive-width dyadic order instance. -/
public theorem problem_valid_iff {N x t n r : Nat} (A : ModExpOracleAccess N x t n)
    (state : ExecutionState (Execution.Store Sampling.pre) Sampling.pre.register) :
    (problem A r).valid state ↔ 0 < t ∧ OrderFinding.Input N x r ∧ r ∣ 2 ^ t := Iff.rfl

/-- The accepted unsigned result is precisely an exact-grid sample of the original order. -/
public theorem problem_accepts_unsigned_iff {N x t n r : Nat}
    (A : ModExpOracleAccess N x t n) (initial : Execution.Store Sampling.pre)
    (word : Fin (2 ^ t)) :
    (problem A r).accepts initial (.unsignedWord word) ↔
      ∃ sample : Fin r, word.val = sample.val * (2 ^ t / r) := Iff.rfl

/-- Execute original order sampling and actual stored-bit decoding with complete live Output. -/
public def algorithm {N x t n : Nat} (A : ModExpOracleAccess N x t n) :
    Algorithm .quantum Sampling.pre (Exact.post t n) (.unsignedWord t) where
  run := Exact.run A

private theorem actual_success {N x t n r : Nat} (A : ModExpOracleAccess N x t n)
    (hinput : OrderFinding.Input N x r) (dyadic : r ∣ 2 ^ t)
    {Reference : Register} (input : Execution.Input Sampling.pre Reference) :
    ((Exact.run A).relationalDistribution input).toOuterMeasure
      {pair | (problem A r).accepts pair.1 pair.2} = 1 := by
  have projection : ((Exact.run A).relationalDistribution input).toOuterMeasure
      {pair | (problem A r).accepts pair.1 pair.2} =
        ((Exact.run A).outputDistribution input).toOuterMeasure
          {output | SuccessfulOutcome r output} := by
    simp only [AlgorithmRun.relationalDistribution, AlgorithmRun.outputDistribution,
      PMF.toOuterMeasure_map_apply]
    rfl
  rw [projection]
  exact Exact.successProbability_eq_one A hinput dyadic input

/-- The complete actual run solves exact dyadic sampling on the original source domain. -/
public theorem main {N x t n r : Nat} (A : ModExpOracleAccess N x t n) :
    ∃ candidate : Algorithm .quantum Sampling.pre (Exact.post t n) (.unsignedWord t),
      Algorithm.Solves candidate (problem A r) := by
  refine ⟨algorithm A, ?_⟩
  constructor
  · intro Reference input valid
    rcases valid with ⟨_positiveWidth, hinput, dyadic⟩
    exact le_of_eq (actual_success A hinput dyadic input).symm
  · intro _Reference _input _valid requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid
    exact Exact.code_borrowedRestored A
      (input.state.mapClassical (fun store => (store, store)))
  · intro _Reference _input _valid path _supported
    exact Exact.code_events_le A path
  · intro _Reference _input _valid path _supported
    exact Exact.code_residentSpace A path
  · intro _Reference _input _valid path _supported
    exact Exact.code_auxiliarySpace A path
  · intro _Reference _input _valid path _supported
    exact Exact.code_depth_le A path

end

end QuantumAlg.OrderFinding
