/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Success
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Success

/-!
# Independent complete first-round protocol

The first quantum cycle includes genuine storage allocation, latch clearing,
physical preparation, source sampling, selected query, native factor recovery,
feedback and complete reset. It accepts the original caller without a supplied
prepared state, selector or success witness.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- Read the existing first-round latch and selected word and prescribe its full zero bank. -/
def stateRequirement (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) : StateRequirement base (Iteration.context (bank base noQuantum N) N) :=
  .marginal Finset.univ (Round.resultRead (bank base noQuantum N) N (cells base noQuantum N))
    (fun _ _ => .pure (NormalizedVector.ket
      ((Iteration.context (bank base noQuantum N) N).quantumLayout.restrictSelectedBasis
        Finset.univ (Iteration.context (bank base noQuantum N) N).quantumLayout.zeroLabel)))

/-- One complete first declared-query attempt from the genuine original caller.

**Input.**
- The original modulus, arbitrary classical caller state and external
  reference, with no incoming quantum systems or prepared bank.
**Output.**
- The actual accepted bit and selected factor word, every live original and
  retained source entry, the same physical bank in predetermined zero and
  every restored borrowed correlation.
**Resource budget.**
- Actual persistent allocation, the paid latch clear and one preparation per
  bank wire, followed by all source sampling, declared query, native inverse
  Fourier gates, phase readout and packing, recovery, feedback and reset.
- Both live-space ledgers include the caller, all five persistent heads,
  the owned physical bank, complete retained results and simultaneous scratch.
- Complete first-cycle quantum time uses the canonical event duration and
  the same complete closed allowance.
**Success.**
- The original rational one-attempt threshold for a factor of the unknown
  distinct-prime semiprime, including even moduli and nonunit samples.
**Source.**
- [Sho95, source.tex:1124-1169,1183-1245] for actual sampling and recovery.
- [dW19, qcnotes.tex:2203-2225] for the declared XOR query interpretation.
-/
def problem (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) :
    Problem (executionModel N) base
      (Iteration.context (bank base noQuantum N) N)
      (.product .bit (.unsignedWord (modulusBits N))) where
  Witness := NumberTheory.Factoring.SemiprimeFactorModel N
  valid := fun actual _ _ => actual.quantum =
    DeclaredSource.interpretation (sourceBounds input) (phaseBits N)
  initialization := fun _ _ _ => True
  accepts := fun _ witness _ value => Round.accepts witness value
  successLB := fun _ _ =>
    ⟨Probability.honestAttemptSuccessFloor N, honestFloor_le_one input⟩
  states := fun _ _ => [stateRequirement base noQuantum N]
  resources :=
    { events := firstEnvelope N
      resident := base.residentSpace + firstAdditionalSpace N
      auxiliary := base.auxiliarySpace + firstAdditionalSpace N }
  quantumTimeLimit := ResourcePool.weightedCount Resource.Event.quantumDuration
    (firstEnvelope N)

/-- Genuine initialization and the entire first attempt form one actual computation. -/
def algorithm (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)
    (input : Input N) :
    Algorithm (executionModel N) base
      (Iteration.context (bank base noQuantum N) N)
      (.product .bit (.unsignedWord (modulusBits N))) where
  run := run base noQuantum N input

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
