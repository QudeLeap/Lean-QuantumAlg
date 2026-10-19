/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Core.Algorithm.Solves

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.State
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.QuantumTime
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

/-!
# RSA factoring with one recycled control qubit

The public modulus and real failure target determine the actual chronological
program. Every batch draws its own original residue sample, executes sixteen
members and completes lattice recovery. Each member reuses one control qubit
across both exponent streams; the arithmetic accumulator remains coherent.
Actual measurements, paid output packing, parallel bank reset and seed reload
belong to the same program. All future classical destinations are allocated
before the sole quantum bank, and their simultaneous capacity is charged.

The reduction is [EH17, source.tex:878-966]. Quantum sampling and lattice
recovery are [E23, arxiv-v5.tex:218-299,329-355]. The measured Fourier identity
is [GN96, 9511007.tex:100-114,246-266]. Native resource bounds are implementation
refinements of these mathematical constructions.
-/

namespace QuantumAlg.Factoring.RSA

noncomputable section

open EkeraHastadStyle.Canonical

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Complete single-control factoring on the original good-key branch.

**Input.**
- The executable inputs are the public modulus and a real target $0<\eta<1$.
  The proof-side key retains the original equal-width prime conditions.
- Every normalized incoming classical state and arbitrary external reference
  is admitted. The program internally prepares its sole quantum bank.
**Output.**
- The actual stored output is an optional checked factor of the original key.
- Every outcome restores the complete bank jointly with the original reference;
  mandatory borrowed restoration is an independent contract gate.
**Resource budget.**
- Write $k=\lceil\log(\eta/2)/\log(147/256)\rceil_{\mathbb N}$,
  $M=\lceil\log_2 N\rceil$, $d=m+2\ell$ and $w=\lceil\log_2(N+1)\rceil$.
  The same chronological program performs $16k$ members using $1+2w$ qubits.
- If $A$ is the closed recovery-workspace allocation, its added classical
  capacity is $k(19M+16d+2)+M+1+d+\max(9M+14,A+8M+2,1+2w,2M+2)$.
  Resident and auxiliary caller storage are added separately.
- Gate and classical-operation ceilings come from the independent whole-run
  event pool. Quantum time includes the initial seed load and every member's
  arithmetic, adaptive readout, measured reset and reload.
**Success.**
- Conditional good-key success is at least $1-\eta/2$.
- The separate ordered-key result charges exceptional-key loss once and proves
  success at least $1-\eta$ eventually in the original prime width.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- [GN96, 9511007.tex:100-114,246-266] supplies the measured Fourier identity.
- Native resource limits refine the same complete physical execution.
-/
public def problem (N : Nat) (η : Real) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Recycling.Program.outputContext base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := GoodKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ model _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := fun _ _ => ⟨1 - ENNReal.ofReal (η / 2), tsub_le_self⟩
  states := fun _ _ => [Recycling.Program.stateRequirement base noQuantum N
    (NativeFiniteRetry.Calibration.retryCount η)]
  resources :=
    { events := Recycling.Program.eventBudget N (NativeFiniteRetry.Calibration.retryCount η)
      resident := base.residentSpace +
        Recycling.Program.spaceLimit N (NativeFiniteRetry.Calibration.retryCount η)
      auxiliary := base.auxiliarySpace +
        Recycling.Program.spaceLimit N (NativeFiniteRetry.Calibration.retryCount η) }
  quantumTimeLimit := Recycling.Program.quantumTimeLimit N
    (NativeFiniteRetry.Calibration.retryCount η)

private lemma realTarget_solves {N : Nat} (specification : Input N)
    (η : Real) (positive : 0 < η) :
    (Recycling.Program.algorithm base noQuantum specification
      (NativeFiniteRetry.Calibration.retryCount η)).Solves
      (problem base noQuantum N η) := by
  refine { Recycling.Program.rsaRecyclingParent_algorithm_solves_fixedRound base noQuantum
    specification
    (NativeFiniteRetry.Calibration.retryCount η) with success := ?_ }
  intro environment key Reference input _valid _initialized
  change GoodKeyModel N at key
  change 1 - ENNReal.ofReal (η / 2) ≤
    ((Recycling.Program.algorithm base noQuantum specification
      (NativeFiniteRetry.Calibration.retryCount η)).relationalDistribution environment
        input).toOuterMeasure
      {pair | (Recycling.Program.fixedRoundProblem base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η)).accepts environment key pair.1 pair.2}
  rw [Recycling.Program.rsaRecyclingParent_relational_probability
    (environment := environment) base noQuantum key
    (NativeFiniteRetry.Calibration.retryCount η) input]
  exact Recycling.Program.rsaRecyclingParent_run_successProbability_ge_halfTarget
    base noQuantum key η positive input

/-- A complete actual algorithm solves the independent real-target factoring problem. -/
public theorem main {N : Nat} (specification : Input N)
    (η : Real) (etaPositive : 0 < η) (_etaLessOne : η < 1) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Recycling.Program.outputContext base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N),
      candidate.Solves (problem base noQuantum N η) :=
  ⟨Recycling.Program.algorithm base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount η),
    realTarget_solves base noQuantum specification η etaPositive⟩

end

end QuantumAlg.Factoring.RSA
