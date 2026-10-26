/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.RSA.Configuration

public import QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Core.Algorithm.Solves

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Endpoint
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.State
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Events
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Space
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.QuantumTime
import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

/-!
# RSA factoring with one recycled control qubit

The public modulus and real failure target determine the actual chronological
program. Every batch draws its own original residue sample, executes the
configured members (sixteen by default), and completes lattice recovery.
Measured static arithmetic reuses two clean adder systems and one clean flag,
with actual H/MZ/reset and paid phase correction on every retained record.
Each member reuses one control qubit across both exponent streams; the
arithmetic accumulator remains coherent.
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

variable [configuration : Configuration]

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
  For configured batch size $s$ (default $16$), the same chronological program
  performs $sk$ members using $2w+4$ qubits.
- If $A$ is the closed recovery-workspace allocation, its added classical
  capacity is $k(19M+sd+2)+M+1+d+(w-2)+\max(9M+14,A+8M+2,2w+4,2M+2)$.
  Resident and auxiliary caller storage are added separately.
- Gate and classical-operation ceilings come from the independent whole-run
  event pool. Quantum time includes the initial seed load and every member's
  measured arithmetic, adaptive readout, complete physical reset and reload.
- The tight original key-domain arithmetic caps are $28w^2-45w$ Toffoli,
  $108w^2-178w$ CNOT and $24w^2-32w$ single-qubit gates per multiplier.
  Full-input resource observations use a separate independent general cap.
**Success.**
- Conditional good-key success is at least $1-\eta/2$.
- The separate ordered-key result charges exceptional-key loss once and proves
  success at least $1-\eta$ eventually in the original prime width.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- [GN96, 9511007.tex:100-114,246-266] supplies the measured Fourier identity.
- [G25, main.tex:199-295,354-360] supplies the measured arithmetic construction;
  the displayed polynomial budgets are derived from its actual native generator.
-/
public def problem (N : Nat) (η : Real) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Measured.Program.outputContext base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  Witness := GoodKeyModel N
  valid := fun _ _ _ => True
  initialization := fun _ _ _ => True
  accepts := fun _ model _ output => NativeRetrySelection.decodeFactor output ∈
    NativeBatchSuccess.accepts model
  successLB := fun _ _ => ⟨1 - ENNReal.ofReal (η / 2), tsub_le_self⟩
  states := fun _ _ => [Measured.Program.stateRequirement base noQuantum N
    (NativeFiniteRetry.Calibration.retryCount η)]
  resources :=
    { events := Measured.Program.eventBudget N (NativeFiniteRetry.Calibration.retryCount η)
      resident := base.residentSpace +
        Measured.Program.spaceLimit N (NativeFiniteRetry.Calibration.retryCount η)
      auxiliary := base.auxiliarySpace +
        Measured.Program.spaceLimit N (NativeFiniteRetry.Calibration.retryCount η) }
  quantumTimeLimit := Measured.Program.quantumTimeLimit N
    (NativeFiniteRetry.Calibration.retryCount η)

private lemma realTarget_solves {N : Nat} (specification : Input N)
    (η : Real) (positive : 0 < η) :
    (Measured.Program.algorithm base noQuantum specification
      (NativeFiniteRetry.Calibration.retryCount η)).Solves
      (problem base noQuantum N η) := by
  refine { Measured.Program.rsaMeasuredParent_algorithm_solves_fixedRound base noQuantum
    specification
    (NativeFiniteRetry.Calibration.retryCount η) with success := ?_ }
  intro environment key Reference input _valid _initialized
  change GoodKeyModel N at key
  change 1 - ENNReal.ofReal (η / 2) ≤
    ((Measured.Program.algorithm base noQuantum specification
      (NativeFiniteRetry.Calibration.retryCount η)).relationalDistribution environment
        input).toOuterMeasure
      {pair | (Measured.Program.fixedRoundProblem base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η)).accepts environment key pair.1 pair.2}
  rw [Measured.Program.rsaMeasuredParent_relational_probability
    (environment := environment) base noQuantum specification key
    (NativeFiniteRetry.Calibration.retryCount η) input]
  exact Measured.Program.rsaMeasuredParent_run_successProbability_ge_halfTarget
    base noQuantum specification key η positive input

/-- A complete actual algorithm solves the independent real-target factoring problem. -/
public theorem main {N : Nat} (specification : Input N)
    (η : Real) (etaPositive : 0 < η) (_etaLessOne : η < 1) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (Measured.Program.outputContext base noQuantum N
        (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N),
      candidate.Solves (problem base noQuantum N η) :=
  ⟨Measured.Program.algorithm base noQuantum specification
    (NativeFiniteRetry.Calibration.retryCount η),
    realTarget_solves base noQuantum specification η etaPositive⟩

end

end QuantumAlg.Factoring.RSA
