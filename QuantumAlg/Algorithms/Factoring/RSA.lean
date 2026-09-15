/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State

public import QuantumAlg.Algorithms.Factoring.Common
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Target
public import QuantumAlg.Core.Algorithm.Solves

/-!
# RSA factoring by actual finite Ekerå–Håstad execution

The implementation receives the public modulus and rational failure target.
The factors, same-width encoding and original exceptional-key condition are
proof-side data. Each batch executes the actual residue sampler, sixteen
compiled arithmetic members and complete lattice recovery. Later batches
reuse the measured quantum bank; actual retained selection returns the first
factor. The main theorem includes both the complete conditional execution
contract and the original eventual guarantee over uniform ordered keys.

The RSA reduction is [EH17, source.tex:878-966]. The quantum construction
and measurement law are [E23, arxiv-v5.tex:218-299]; lattice post-processing
starts at [E23, arxiv-v5.tex:329-355]. The compiled native event and storage
bounds are proved implementation refinements of this mathematical route.
-/

namespace QuantumAlg.Factoring.RSA

open EkeraHastadStyle EkeraHastadStyle.Canonical

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Complete native RSA factoring on an original good-key branch.

**Input.**
- The executable input is the public modulus $N$ and rational failure target
  $0 < \eta \le 1$. Distinct odd equal-width primes, exact doubled product width,
  the effective-width bound and the original key condition certify correctness.
- Every normalized incoming classical state and arbitrary external reference
  is admitted; the implementation internally prepares its quantum bank.
**Output.**
- An actual stored optional unsigned factor word; acceptance means one of the
  two declared primes. Every live cell and quantum wire occurs in the Output.
- On success and failure, the entire bank has its original seed jointly with
  the complete incoming reference. Borrowed restoration is a separate gate.
**Resource budget.**
- The explicit finite count is $k = \max\{1, \lceil\log(2/\eta)/\log(256/147)\rceil\}$.
  It executes $16k$ complete quantum members and all classical recovery.
- Write $M = \lceil\log_2 N\rceil$ and $d = m + 2\ell$; let $A$ denote
  the closed lattice-workspace allocation formula.
  Additional classical capacity is $A + 36M + 17d + 19 + k(19M + 16d + 2)$.
- The one shared quantum bank has $m + 2\ell + 2w$ qubits, where
  $m=\lfloor M/2\rfloor+1$, $\ell=\lfloor(m+1)/2\rfloor$ and
  $w=\lceil\log_2(N+1)\rceil$.
  Caller classical storage remains counted.
- Independent native event pools are the first-batch pool plus $k-1$ reused
  batch pools plus the actual chronological selector pool. All preparations,
  stored measurements, corrections, reset work and retained results are counted.
- Serial unit-event depth is $D_0 + (k-1)D_r + 3k + 1$, where $D_0$ and $D_r$
  are the independent first/reused complete-batch depth formulas.
**Success.**
- Conditional success is at least $1-\eta/2$. The main theorem also proves
  success at least $1-\eta$ over the original uniform ordered key distribution
  for all sufficiently large prime widths. The exceptional-key loss is charged
  once outside the retry power. No all-width arbitrary-target claim is made.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- Native execution, complete state restoration and independent resource
  formulas are the implementation refinement proved here.
-/
@[expose] public def problem {N : Nat} (model : GoodKeyModel N) (budget : FailureBudget) :
    Problem .quantum base
      (NativeFiniteRetry.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  accepts := fun _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := ⟨1 - ENNReal.ofReal (budget.value / 2), tsub_le_self⟩
  states := [NativeFiniteRetry.stateRequirement base noQuantum N
    (NativeFiniteRetry.Calibration.retryCount budget)]
  resources :=
    { events := NativeFiniteRetry.eventEnvelope N (NativeFiniteRetry.Calibration.retryCount budget)
      resident := base.residentSpace +
        NativeFiniteRetry.additionalSpace N (NativeFiniteRetry.Calibration.retryCount budget)
      auxiliary := base.auxiliarySpace +
        NativeFiniteRetry.additionalSpace N (NativeFiniteRetry.Calibration.retryCount budget) }
  depth := .quantum (fun _ => 1)
    (NativeFiniteRetry.depthBound N (NativeFiniteRetry.Calibration.retryCount budget))

/-- One actual finite run uses only the original public-modulus assumptions and failure target. -/
public def algorithm {N : Nat} (specification : Canonical.Input N) (budget : FailureBudget) :
    Algorithm .quantum base
      (NativeFiniteRetry.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := NativeFiniteRetry.run base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount budget)

/-- The named public candidate satisfies every state, probability and native resource gate. -/
public theorem algorithm_solves {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
      (problem base noQuantum model budget) :=
  NativeFiniteRetry.algorithm_solves base noQuantum model budget wellFormed

/-- The public resident classical budget exposes the independent finite-count scalar formula. -/
public theorem problem_resident_classicalBits {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.resident .classicalBits =
      base.residentSpace .classicalBits +
        NativeFiniteRetry.classicalBitBound N
          (NativeFiniteRetry.Calibration.retryCount budget) := by
  exact congrArg (fun bits => base.residentSpace .classicalBits + bits)
    (NativeFiniteRetry.additionalSpace_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount budget))

/-- The public auxiliary classical budget retains the same independent temporary allowance. -/
public theorem problem_auxiliary_classicalBits {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.auxiliary .classicalBits =
      base.auxiliarySpace .classicalBits +
        NativeFiniteRetry.classicalBitBound N
          (NativeFiniteRetry.Calibration.retryCount budget) := by
  exact congrArg (fun bits => base.auxiliarySpace .classicalBits + bits)
    (NativeFiniteRetry.additionalSpace_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount budget))

/-- The public resident quantum budget charges one bank at every positive calibrated count. -/
public theorem problem_resident_qubits {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.resident (.quantumSystems 2) =
      base.residentSpace (.quantumSystems 2) +
        NativeFiniteRetry.qubitBound N (NativeFiniteRetry.Calibration.retryCount budget) := by
  exact congrArg (fun qubits => base.residentSpace (.quantumSystems 2) + qubits)
    (NativeFiniteRetry.additionalSpace_qubits N (NativeFiniteRetry.Calibration.retryCount budget))

/-- The public auxiliary quantum coordinate is the same one-bank independent allowance. -/
public theorem problem_auxiliary_qubits {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.auxiliary (.quantumSystems 2) =
      base.auxiliarySpace (.quantumSystems 2) +
        NativeFiniteRetry.qubitBound N (NativeFiniteRetry.Calibration.retryCount budget) := by
  exact congrArg (fun qubits => base.auxiliarySpace (.quantumSystems 2) + qubits)
    (NativeFiniteRetry.additionalSpace_qubits N (NativeFiniteRetry.Calibration.retryCount budget))

/-- Mathematical key averaging observes that same public algorithm on each generated modulus.
The arbitrary input family allows correlations between the key and the initial reference. -/
public def keygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference) :
    PMF (Nat × Nat × Option Nat) :=
  (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((algorithm base noQuantum (inputOfKeyPair pair) budget).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The public key average is the previously established actual finite-run average. -/
theorem keygenOutput_eq (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference) :
    keygenOutput base noQuantum bitWidth nonempty budget inputs =
      NativeKeyGeneration.outputDistribution base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount budget) inputs := rfl

/-- The full target concerns the original uniform keys and the named actual public algorithm. -/
@[expose] public def AsymptoticKeygenSuccess (budget : FailureBudget) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth),
      QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference),
        FailureBudget.successThreshold budget ≤
          (keygenOutput base noQuantum bitWidth nonempty budget inputs).toOuterMeasure
            NativeKeyGeneration.successEvent

/-- The original eventual full target holds for the actual public key average. -/
public theorem asymptoticKeygenSuccess (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    AsymptoticKeygenSuccess base noQuantum budget := by
  filter_upwards [NativeKeyGeneration.eventually_success_ge_target
    base noQuantum budget wellFormed] with bitWidth success
  intro nonempty effective Reference inputs
  rw [keygenOutput_eq]
  exact success nonempty effective Reference inputs

/-- RSA factoring combines a complete actual conditional contract with the original full
uniform-key guarantee, retaining the finite repetition and rational failure parameters. -/
public theorem main {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
        (problem base noQuantum model budget) ∧
      AsymptoticKeygenSuccess base noQuantum budget :=
  ⟨algorithm_solves base noQuantum model budget wellFormed,
    asymptoticKeygenSuccess base noQuantum budget wellFormed⟩

end

end QuantumAlg.Factoring.RSA
