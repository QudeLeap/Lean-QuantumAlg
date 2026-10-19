/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.State
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Success
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent real-target declared Shor machine protocol

Only the original modulus and failure target determine the real execution.
Unknown distinct primes occur in the theorem-side accepted result alone. The
machine internally initializes all storage, prepares one bank, executes every
requested complete attempt and packs the actual first success exactly once.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget

open Execution

noncomputable section

private def successBound (η : Real) (positive : 0 < η) :
    ProbabilityLowerBound where
  value := ENNReal.ofReal (1 - η)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    linarith

/-- Complete declared-query factorization from the original classical caller.

**Input.**
- A known product of unknown distinct primes, an original real failure
  target and arbitrary joint classical caller, service and external reference
  state, with no incoming quantum bank or factor witness.
**Output.**
- The actual optional prime-factor word and the complete live output manifest.
- Every optional result fiber has the same predetermined full physical zero
  bank jointly with the original reference; borrowed correlations are restored.
**Resource budget.**
- One genuine initializer, every original requested complete round and one
  terminal option pack. Each round includes real source sampling, one granted
  query, native Fourier peripherals, actual readout, full recovery, feedback
  and paid reset.
- Both space budgets include the caller, all five persistent heads, the one
  owned bank, all surviving source cells and simultaneous full native scratch.
- Whole chronological depth evaluates the entire actual dependency path
  under the canonical quantum duration and the complete independent event ledger.
**Success.**
- The original declared prime factor is returned with probability at least
  the original real failure target's success threshold.
**Source.**
- [Sho95, source.tex:1124-1169,1183-1245] for sampling, amplification and recovery.
- [dW19, qcnotes.tex:2203-2225] for the declared XOR query interpretation.
-/
def countProblem (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) (count : Nat) (η : Real)
    (positive : 0 < η) :
    Problem (executionModel N) base
      (context base noQuantum N count)
      (.option (.unsignedWord (modulusBits N))) where
  Witness := NumberTheory.Factoring.SemiprimeFactorModel N
  valid := fun actual _ _ => actual.quantum =
    DeclaredSource.interpretation (sourceBounds input) (phaseBits N)
  initialization := fun _ _ _ => True
  accepts := fun _ witness _ output => Probability.ReturnedDeclaredFactor witness output
  successLB := fun _ _ => successBound η positive
  states := fun _ _ => [stateRequirement base noQuantum N count]
  resources :=
    { events := eventEnvelope N count
      resident := base.residentSpace + additionalSpace N count
      auxiliary := base.auxiliarySpace + additionalSpace N count }
  quantumTimeLimit := ResourcePool.weightedCount Resource.Event.quantumDuration
    (eventEnvelope N count)

/-- The same actual initialized finite execution returns its sole terminal packed factor. -/
def countAlgorithm (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) (count : Nat) :
    Algorithm (executionModel N) base
      (context base noQuantum N count)
      (.option (.unsignedWord (modulusBits N))) where
  run := run base noQuantum N input count

/-- Select the complete independent protocol at the real-target repetition count. -/
def problem (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) (η : Real) (positive : 0 < η) :=
  countProblem base noQuantum N input (repetitionCount N η) η positive

/-- Run the same complete machine for exactly the direct logarithmic count. -/
def algorithm (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) (η : Real) :=
  countAlgorithm base noQuantum N input (repetitionCount N η)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine.RealTarget
