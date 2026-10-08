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
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability
public import QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
public import QuantumAlg.Core.Algorithm.CyclePlan
public import QuantumAlg.Core.Execution.CycleSchedule
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.Weighted

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.SevenCoordinates
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

open EkeraHastadStyle EkeraHastadStyle.Canonical ShortDLP.CompiledMAU

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
    Problem RuntimeRound.model base
      (NativeFiniteRetry.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeFiniteRetry.problem base noQuantum model budget

/-- The same actual algorithm at any specified finite batch count. -/
public def algorithmAtCount {N : Nat} (specification : Canonical.Input N) (count : Nat) :
    Algorithm RuntimeRound.model base
      (NativeFiniteRetry.context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeFiniteRetry.algorithm base noQuantum specification count

/-- Calibration specializes the same arbitrary-count algorithm on the original input. -/
@[expose] public def algorithm {N : Nat} (specification : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm RuntimeRound.model base
      (NativeFiniteRetry.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  algorithmAtCount base noQuantum specification
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

/-- Independently specified all-key complete-batch boundaries at that count. -/
public def cycleProblemAtCount {N : Nat} (specification : Canonical.Input N)
    (count : Nat) :
    CycleProblem RuntimeRound.model base
      (NativeFiniteRetry.context base noQuantum N count)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeCycles.AllKeysFinite.problem base noQuantum specification count

/-- The named actual run follows those complete-batch boundaries. -/
public def cycleCertificateAtCount {N : Nat} (specification : Canonical.Input N)
    (count : Nat) :
    Algorithm.CycleSolves (algorithmAtCount base noQuantum specification count)
      (cycleProblemAtCount base noQuantum specification count) :=
  NativeCycles.AllKeysFinite.certificate base noQuantum specification count

/-- The calibrated public RSA run follows the same completed-batch schedule. -/
@[expose] public def cycleCertificate {N : Nat} (specification : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm.CycleSolves (algorithm base noQuantum specification budget)
      (cycleProblemAtCount base noQuantum specification
        (NativeFiniteRetry.Calibration.retryCount budget)) :=
  cycleCertificateAtCount base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount budget)

/-- Symbolic native gate ceiling for any count and gate coordinate. -/
public def gateCountBoundAtCount (N count : Nat)
    (coordinate : AlgorithmGate.Coordinate) : Nat :=
  NativeFiniteRetry.gateCountBound N count coordinate

/-- Symbolic complete-cycle ceiling, with zero depth for zero batches. -/
public def cycleDepthBoundAtCount (N count : Nat) : Nat :=
  NativeCycles.Finite.maximumCycleScalarBound N count

/-- Symbolic ceiling for literal classical operations on the actual path. -/
public def classicalOperationBoundAtCount (N count : Nat) : Nat :=
  NativeFiniteRetry.scalarClassicalOperationBound N count

/-- Independent scalar ceilings for the seven observed resource coordinates.
Resident and auxiliary classical storage retain separate bounds. -/
public structure CoordinateLimits where
  /-- Peak resident two-level quantum systems, including the caller. -/
  qubits : Nat
  /-- Total Toffoli gates on the complete execution path. -/
  toffoli : Nat
  /-- Total CNOT gates on the complete execution path. -/
  cnot : Nat
  /-- Total single-qubit gates on the complete execution path. -/
  singleQubit : Nat
  /-- Maximum unit-event depth of a complete certified cycle. -/
  cycleDepth : Nat
  /-- Peak resident classical bits, including the caller. -/
  residentClassicalBits : Nat
  /-- Peak auxiliary classical bits, including the caller. -/
  auxiliaryClassicalBits : Nat
  /-- Total literal classical operations on the complete execution path. -/
  classicalOperations : Nat

/-- Parameter-only ceilings, including the caller's existing storage. -/
@[expose] public def coordinateLimitsAtCount (N count : Nat) : CoordinateLimits where
  qubits := base.residentSpace (.quantumSystems 2) + NativeFiniteRetry.qubitBound N count
  toffoli := gateCountBoundAtCount N count .toffoli
  cnot := gateCountBoundAtCount N count .cnot
  singleQubit := gateCountBoundAtCount N count .singleQubit
  cycleDepth := cycleDepthBoundAtCount N count
  residentClassicalBits := base.residentSpace .classicalBits +
    NativeFiniteRetry.classicalBitBound N count
  auxiliaryClassicalBits := base.auxiliarySpace .classicalBits +
    NativeFiniteRetry.classicalBitBound N count
  classicalOperations := classicalOperationBoundAtCount N count

/-- Seven bounds on one actual path and its explicit complete-cycle certificate.
Generic and fixed ceilings instantiate this same observation contract. -/
public structure SevenCoordinateBoundsAtCount {N : Nat}
    (specification : Canonical.Input N) (count : Nat)
    (cycles : Algorithm.CycleSolves (algorithmAtCount base noQuantum specification count)
      (cycleProblemAtCount base noQuantum specification count))
    (limits : CoordinateLimits)
    (path : (algorithmAtCount base noQuantum specification count).run.code.Path) : Prop where
  qubits :
    (algorithmAtCount base noQuantum specification count).run.code.peakResidentSpace
      path (.quantumSystems 2) ≤
        limits.qubits
  toffoli :
    ResourcePool.count (model := RuntimeRound.model) (.gate .toffoli)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.toffoli
  cnot :
    ResourcePool.count (model := RuntimeRound.model) (.gate .cnot)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.cnot
  singleQubit :
    ResourcePool.count (model := RuntimeRound.model) (.gate .singleQubit)
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.singleQubit
  cycleDepth :
    cycles.maximumCycleDepth (fun _ => 1) path ≤ limits.cycleDepth
  classicalBits :
    ((algorithmAtCount base noQuantum specification count).run.code.peakResidentSpace
      path .classicalBits ≤ limits.residentClassicalBits) ∧
    (algorithmAtCount base noQuantum specification count).run.code.peakAuxiliarySpace
      path .classicalBits ≤ limits.auxiliaryClassicalBits
  classicalOperations :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithmAtCount base noQuantum specification count).run.code.resourcePool path) ≤
        limits.classicalOperations

/-- All original modulus inputs and all finite counts satisfy every coordinate. -/
public theorem algorithmAtCount_sevenCoordinates {N : Nat}
    (specification : Canonical.Input N) (count : Nat)
    (path : (algorithmAtCount base noQuantum specification count).run.code.Path) :
    SevenCoordinateBoundsAtCount base noQuantum specification count
      (cycleCertificateAtCount base noQuantum specification count)
      (coordinateLimitsAtCount base N count) path := by
  rcases NativeFiniteRetry.sevenCoordinates base noQuantum specification count path with
    ⟨qubits, toffoli, cnot, singleQubit, cycleDepth,
      classicalBits, classicalOperations⟩
  exact ⟨qubits, toffoli, cnot, singleQubit, cycleDepth,
    classicalBits, classicalOperations⟩

/-- Calibration specializes the arbitrary-count contract without duplicating its fields. -/
public abbrev SevenCoordinateBounds {N : Nat} (specification : Canonical.Input N)
    (budget : FailureBudget)
    (cycles : Algorithm.CycleSolves (algorithm base noQuantum specification budget)
      (cycleProblemAtCount base noQuantum specification
        (NativeFiniteRetry.Calibration.retryCount budget)))
    (path : (algorithm base noQuantum specification budget).run.code.Path) : Prop :=
  SevenCoordinateBoundsAtCount base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount budget) cycles
    (coordinateLimitsAtCount base N (NativeFiniteRetry.Calibration.retryCount budget)) path

/-- Every path of the public finite RSA algorithm obeys the same seven bounds. -/
public theorem algorithm_sevenCoordinates {N : Nat} (specification : Canonical.Input N)
    (budget : FailureBudget)
    (path : (algorithm base noQuantum specification budget).run.code.Path) :
    SevenCoordinateBounds base noQuantum specification budget
      (cycleCertificate base noQuantum specification budget) path :=
  algorithmAtCount_sevenCoordinates base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount budget) path

/-- Mathematical key averaging observes that same public algorithm on each generated modulus.
The arbitrary input family allows correlations between the key and the initial reference. -/
public def keygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    PMF (Nat × Nat × Option Nat) :=
  (QuantumAlg.RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((algorithm base noQuantum (inputOfKeyPair pair) budget).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The public key average is the previously established actual finite-run average. -/
theorem keygenOutput_eq (bitWidth : Nat)
    (nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput RuntimeRound.model.classicalOracles base Reference) :
    keygenOutput base noQuantum bitWidth nonempty budget inputs =
      NativeKeyGeneration.outputDistribution base noQuantum bitWidth nonempty
        (NativeFiniteRetry.Calibration.retryCount budget) inputs := rfl

/-- The full target concerns the original uniform keys and the named actual public algorithm. -/
@[expose] public def AsymptoticKeygenSuccess (budget : FailureBudget) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (QuantumAlg.RSA.RSAKeyPairBits bitWidth),
      QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : QuantumAlg.RSA.RSAKeyPairBits bitWidth →
          Execution.OracleInput RuntimeRound.model.classicalOracles base Reference),
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

/-- The registered RSA theorem combines the actual all-input completed-cycle
certificate, conditional state/success contract, seven same-path resource
coordinates and original eventual ordered-key guarantee. -/
public theorem main {N : Nat} (model : GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∃ cycles : Algorithm.CycleSolves
        (algorithm base noQuantum model.input budget)
        (cycleProblemAtCount base noQuantum model.input
          (NativeFiniteRetry.Calibration.retryCount budget)),
      Algorithm.Solves (algorithm base noQuantum model.input budget)
          (problem base noQuantum model budget) ∧
        (∀ path : (algorithm base noQuantum model.input budget).run.code.Path,
          SevenCoordinateBounds base noQuantum model.input budget cycles path) ∧
        AsymptoticKeygenSuccess base noQuantum budget :=
  ⟨cycleCertificate base noQuantum model.input budget,
    algorithm_solves base noQuantum model budget wellFormed,
    algorithm_sevenCoordinates base noQuantum model.input budget,
    asymptoticKeygenSuccess base noQuantum budget wellFormed⟩

end

end QuantumAlg.Factoring.RSA
