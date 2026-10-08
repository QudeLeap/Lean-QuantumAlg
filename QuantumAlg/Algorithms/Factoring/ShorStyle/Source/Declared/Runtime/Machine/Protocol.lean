/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.State
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Success
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent original-input declared Shor machine protocol

Only the original modulus and failure target determine the real execution.
Unknown distinct primes occur in the theorem-side accepted result alone. The
machine internally initializes all storage, prepares one bank, executes every
calibrated complete attempt and packs the actual first success exactly once.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

private def successBound (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ProbabilityLowerBound where
  value := FailureBudget.successThreshold budget
  le_one := by
    unfold FailureBudget.successThreshold
    apply ENNReal.ofReal_le_one.mpr
    have nonnegative := FailureBudget.value_nonneg budget wellFormed
    linarith

/-- Complete declared-query factorization from the original classical caller.

**Input.**
- A known product of unknown distinct primes, an original rational failure
  target and arbitrary joint classical caller, service and external reference
  state, with no incoming quantum bank or factor witness.
**Output.**
- The actual optional prime-factor word and the complete live output manifest.
- Every optional result fiber has the same predetermined full physical zero
  bank jointly with the original reference; borrowed correlations are restored.
**Resource budget.**
- One genuine initializer, every original calibrated complete round and one
  terminal option pack. Each round includes real source sampling, one granted
  query, native Fourier peripherals, actual readout, full recovery, feedback
  and paid reset.
- Both space budgets include the caller, all five persistent heads, the one
  owned bank, all surviving source cells and simultaneous full native scratch.
- Whole chronological depth evaluates the entire actual dependency path
  under independently supplied event durations and the complete closed ledger.
**Success.**
- The original declared prime factor is returned with probability at least
  the original rational failure target's success threshold.
**Source.**
- [Sho95, source.tex:1124-1169,1183-1245] for sampling, amplification and recovery.
- [dW19, qcnotes.tex:2203-2225] for the declared XOR query interpretation.
-/
def problem (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed)
    (duration : Resource.Event (executionModel (Probability.Input.ofSemiprimeModel model)) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Problem (executionModel (Probability.Input.ofSemiprimeModel model)) base
      (context base noQuantum N (retryCount N budget))
      (.option (.unsignedWord (modulusBits N))) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ output => Probability.ReturnedDeclaredFactor model output
  successLB := successBound budget wellFormed
  states := [stateRequirement base noQuantum N (retryCount N budget)]
  resources :=
    { events := eventEnvelope (Probability.Input.ofSemiprimeModel model) (retryCount N budget)
      resident := base.residentSpace + additionalSpace N (retryCount N budget)
      auxiliary := base.auxiliarySpace + additionalSpace N (retryCount N budget) }
  depth :=
    { duration := duration
      limit := ResourcePool.weightedCount duration
        (eventEnvelope (Probability.Input.ofSemiprimeModel model) (retryCount N budget))
      classicalQuery_unit := fun coordinate => nomatch coordinate
      quantumQuery_unit := unitQueries }

/-- The same actual initialized finite execution returns its sole terminal packed factor. -/
def algorithm (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget) :
    Algorithm (executionModel (Probability.Input.ofSemiprimeModel model)) base
      (context base noQuantum N (retryCount N budget))
      (.option (.unsignedWord (modulusBits N))) where
  run := run base noQuantum N (Probability.Input.ofSemiprimeModel model) (retryCount N budget)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
