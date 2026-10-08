/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Success.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Space

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Calibration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Space
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Cycle
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Gates
public import QuantumAlg.Algorithms.Factoring.RSA
import all QuantumAlg.Algorithms.Factoring.RSA
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Depth
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Counts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Instances.Native.RSA2048.Parameters
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Program
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.KeyGeneration.Native.Probability
public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Core.Execution.CycleSchedule
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Budget
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Budget
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord

/-!
# Logical-resource estimate for breaking RSA-2048

The actual algorithm receives only the public modulus and executes seven
complete shared batches, hence 112 compiled arithmetic members. The original
ordered same-width prime pair and good-key condition are proof-side data.
Uniform key generation is the original mathematical distribution, followed
by that same named algorithm for each generated modulus.

The complete output retains every live cell and quantum wire. The final bank
is restored jointly with the incoming reference on success and failure;
borrowed restoration remains a separate mandatory execution obligation.
All resource limits are independent budgets for that same finite execution.

The RSA reduction is [EH17, source.tex:878-966]. The quantum construction and
measurement law are [E23, arxiv-v5.tex:218-299]; the lattice post-processing
starts at [E23, arxiv-v5.tex:329-355]. The native implementation and numerical
resource ceilings are formal refinements of this mathematical route.
-/

namespace QuantumAlg.Factoring.RSA2048

open EkeraHastadStyle EkeraHastadStyle.Canonical

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Complete native factoring at the fixed RSA-2048 width.

**Input.**
- The executable input contains only the public modulus $N$. The proof-side
  model has distinct odd exact $1024$-bit primes $p,q$, exact $2048$-bit
  product $N=pq$, and the original good-key condition.
- Every normalized incoming classical state and arbitrary external reference
  is admitted. The actual implementation internally prepares its quantum bank.
**Output.**
- An actual stored optional unsigned factor word; an accepted output is
  $p$ or $q$. The complete Output lists all retained storage and quantum wires.
- On every outcome, the whole bank has its original seed jointly with the
  incoming reference. Borrowed restoration is required independently.
**Resource budget.**
- Seven complete sampled and recovered batches execute $112$ quantum members.
- One bank of $6{,}147$ qubits is reused across all batches.
- Additional classical capacity is $1{,}053{,}148{,}427{,}049$ bits; the caller's
  resident or auxiliary classical storage is added to the corresponding bound.
- The independent native event pool is the first-batch pool plus six reused
  batch pools and the seven-input selector pool. It includes preparation,
  measurements, literal corrections, classical recovery and retained selection.
- Full serial unit-event depth is at most
  $16{,}798{,}844{,}737{,}672{,}601{,}459$. This includes all quantum and classical
  dependencies of the complete seven-batch execution.
- The complete native event count is at most $16{,}798{,}844{,}770{,}992{,}869{,}825$;
  at most $15{,}343{,}042{,}058{,}108{,}937{,}824$ events are literal classical operations.
- These ceilings apply to every original exact-width key, including exceptional keys.
- These are proved ceilings; no execution is asserted to attain a ceiling.
**Success.**
- The original seven-batch conditional floor is at least $0.99$ on good keys.
- The main theorem also gives success at least $0.99$ over the original
  uniform distribution of ordered exact-width keys. The exceptional-key loss
  is charged once outside the conditional seventh power.
**Source.**
- [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
- The fixed state and native resource bounds are implementation refinements
  proved for the complete actual run.
-/
@[expose] public def problem {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (NativeFiniteRetry.context base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  NativeFiniteRetry.budgetedProblem base noQuantum model.1 NativeRSA2048.rounds
    NativeRSA2048.additionalSpace 16_798_844_737_672_601_459

/-- The actual seven-batch algorithm requires only the original public-modulus input. -/
@[expose] public def algorithm {N : Nat} (specification : Canonical.Input N) :
    Algorithm (.quantum AlgorithmGate.model .empty BitWord.model) base
      (NativeFiniteRetry.context base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  RSA.algorithmAtCount base noQuantum specification NativeRSA2048.rounds

-- Reuse the shared seven-batch run without expanding its dependent execution tree.
attribute [local irreducible] NativeFiniteRetry.run NativeFiniteRetry.code NativeFiniteRetry.context

/-- The named algorithm satisfies the complete independent fixed-width problem. -/
public theorem algorithm_solves {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    Algorithm.Solves (algorithm base noQuantum model.1.input)
      (problem base noQuantum model) := by
  exact NativeFiniteRetry.algorithm_solves_budgeted base noQuantum model.1 NativeRSA2048.rounds
    NativeRSA2048.additionalSpace 16_798_844_737_672_601_459
    (le_of_eq (NativeRSA2048.model_additionalSpace_eq model.widthModel))
    (NativeRSA2048.model_depthBound_le model.widthModel)

/-- The independent conditional success threshold is itself at least ninety-nine percent. -/
public theorem problem_successLB_ge_99 {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    ENNReal.ofReal ((99 : Real) / 100) ≤ (problem base noQuantum model).successLB.value := by
  change ENNReal.ofReal ((99 : Real) / 100) ≤
    1 - NativeFiniteRetry.Calibration.batchFailure model.1.bitWidth ^ NativeRSA2048.rounds
  rw [model.2]
  exact NativeRSA2048.Calibration.conditionalSuccess_seven_ge_99

/-- The resident classical budget exposes the independently proved fixed scalar. -/
public theorem problem_resident_classicalBits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum model).resources.resident .classicalBits =
      base.residentSpace .classicalBits + 1_053_148_427_049 := by
  change (base.residentSpace + NativeRSA2048.additionalSpace) .classicalBits = _
  rfl

/-- The auxiliary classical budget counts the same complete temporary allowance. -/
public theorem problem_auxiliary_classicalBits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum model).resources.auxiliary .classicalBits =
      base.auxiliarySpace .classicalBits + 1_053_148_427_049 := by
  change (base.auxiliarySpace + NativeRSA2048.additionalSpace) .classicalBits = _
  rfl

/-- The independent resident quantum allowance is the single shared bank. -/
public theorem problem_resident_qubits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum model).resources.resident (.quantumSystems 2) = 6_147 := by
  have noBase : base.residentSpace (.quantumSystems 2) = 0 := by
    rw [RuntimeCtx.residentSpace_quantumSystems]
    simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions, RuntimeCtx.systemCount,
      noQuantum, List.length_nil, List.ofFn_zero, List.count_nil]
  change base.residentSpace (.quantumSystems 2) + 6_147 = 6_147
  rw [noBase, Nat.zero_add]

/-- The independent auxiliary quantum allowance adds exactly one shared bank. -/
public theorem problem_auxiliary_qubits {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum model).resources.auxiliary (.quantumSystems 2) =
      base.auxiliarySpace (.quantumSystems 2) + 6_147 := by
  change (base.auxiliarySpace + NativeRSA2048.additionalSpace) (.quantumSystems 2) = _
  rfl

/-- The public depth budget is the proved serial ceiling for all quantum and classical events. -/
public theorem problem_wholeRunDepth {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    (problem base noQuantum model).depth.limit = 16_798_844_737_672_601_459 := by
  change (16_798_844_737_672_601_459 : Nat) = _
  rfl

/-- Every path of the named actual algorithm obeys the independent native-event ceiling. -/
public theorem algorithm_eventCount_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    ((algorithm base noQuantum specification).run.code.eventTrace path).length ≤
      16_798_844_770_992_869_825 :=
  NativeRSA2048.run_eventCount_le base noQuantum model specification path

/-- Literal classical operations on each complete path obey their own independent ceiling. -/
public theorem algorithm_classicalOperation_le {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm base noQuantum specification).run.code.resourcePool path) ≤
        15_343_042_058_108_937_824 :=
  NativeRSA2048.run_classicalOperation_le base noQuantum model specification path

/-- Independent budgets on every path of the named algorithm. The original
fixed-width key condition suffices; no probability-side good-key condition is used. -/
@[expose] public def ResourceBounds {N : Nat} (specification : Canonical.Input N) : Prop :=
  ∀ path : (algorithm base noQuantum specification).run.code.Path,
    (algorithm base noQuantum specification).run.code.peakResidentSpace path ≤
        base.residentSpace + NativeRSA2048.additionalSpace ∧
    (algorithm base noQuantum specification).run.code.peakAuxiliarySpace path ≤
        base.auxiliarySpace + NativeRSA2048.additionalSpace ∧
    (algorithm base noQuantum specification).run.code.depth (fun _ => 1) path ≤
        16_798_844_737_672_601_459 ∧
    ((algorithm base noQuantum specification).run.code.eventTrace path).length ≤
        16_798_844_770_992_869_825 ∧
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm base noQuantum specification).run.code.resourcePool path) ≤
        15_343_042_058_108_937_824

/-- All original fixed-width keys, including exceptional keys, obey the displayed ceilings. -/
public theorem algorithm_resourceBounds {N : Nat} (model : NativeRSA2048.FixedWidthModel N)
    (specification : Canonical.Input N) : ResourceBounds base noQuantum specification := by
  intro path
  have resident := NativeFiniteRetry.run_resident_le
    base noQuantum specification NativeRSA2048.rounds path
  have auxiliary := NativeFiniteRetry.run_auxiliary_le
    base noQuantum specification NativeRSA2048.rounds path
  have space := le_of_eq (NativeRSA2048.model_additionalSpace_eq model)
  exact ⟨resident.trans (fun axis => Nat.add_le_add_left (space axis) _),
    auxiliary.trans (fun axis => Nat.add_le_add_left (space axis) _),
    NativeRSA2048.run_unitDepth_le base noQuantum model specification path,
    algorithm_eventCount_le base noQuantum model specification path,
    algorithm_classicalOperation_le base noQuantum model specification path⟩

/-- The independent source-law plan for the named seven-batch execution. -/
@[expose] public def sevenBatchProblem {N : Nat} (specification : Canonical.Input N) :
    CycleProblem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (NativeFiniteRetry.context base noQuantum N NativeRSA2048.rounds)
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  RSA.cycleProblemAtCount base noQuantum specification NativeRSA2048.rounds

/-- The named algorithm follows that plan on every admissible input and reference. -/
@[expose] public def sevenBatchCertificate {N : Nat} (specification : Canonical.Input N) :
    Algorithm.CycleSolves (algorithm base noQuantum specification)
      (sevenBatchProblem base noQuantum specification) :=
  RSA.cycleCertificateAtCount base noQuantum specification NativeRSA2048.rounds

/-- Independent fixed ceilings; the incoming caller's classical storage is retained. -/
@[expose] public def coordinateLimits : RSA.CoordinateLimits where
  qubits := 6_147
  toffoli := 485_267_570_715_131_904
  cnot := 485_267_571_009_651_248
  singleQubit := 485_267_571_158_230_673
  cycleDepth := 2_399_834_962_524_657_350
  residentClassicalBits := base.residentSpace .classicalBits + 1_053_148_427_049
  auxiliaryClassicalBits := base.auxiliarySpace .classicalBits + 1_053_148_427_049
  classicalOperations := 15_343_042_058_108_937_824

/-- The arbitrary-count observation contract at the fixed seven-batch limits.
Its cycle depth observes exactly the supplied physical certificate. -/
public abbrev SevenCoordinateBounds {N : Nat} (specification : Canonical.Input N)
    (cycles : Algorithm.CycleSolves (algorithm base noQuantum specification)
      (sevenBatchProblem base noQuantum specification))
    (path : (algorithm base noQuantum specification).run.code.Path) : Prop :=
  RSA.SevenCoordinateBoundsAtCount base noQuantum specification NativeRSA2048.rounds
    cycles (coordinateLimits base) path

/-- The public seven-batch algorithm has every independent coordinate on one actual path. -/
public theorem algorithm_sevenCoordinates {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) (specification : Canonical.Input N)
    (path : (algorithm base noQuantum specification).run.code.Path) :
    SevenCoordinateBounds base noQuantum specification
      (sevenBatchCertificate base noQuantum specification) path := by
  rcases RSA.algorithmAtCount_sevenCoordinates base noQuantum specification
      NativeRSA2048.rounds path with
    ⟨qubits, toffoli, cnot, singleQubit, cycleDepth,
      ⟨residentBits, auxiliaryBits⟩, classicalOperations⟩
  have noBase : base.residentSpace (.quantumSystems 2) = 0 := by
    rw [RuntimeCtx.residentSpace_quantumSystems]
    simp only [QuantumLayout.dimensionCount, QuantumLayout.dimensions, RuntimeCtx.systemCount,
      noQuantum, List.length_nil, List.ofFn_zero, List.count_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits, noBase, Nat.zero_add,
      NativeRSA2048.model_qubitBound_eq model, NativeRSA2048.qubitBound] using qubits
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits, RSA.gateCountBoundAtCount,
      NativeRSA2048.model_gateCountBound_eq model .toffoli,
      NativeRSA2048.gateCountBound] using toffoli
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits, RSA.gateCountBoundAtCount,
      NativeRSA2048.model_gateCountBound_eq model .cnot,
      NativeRSA2048.gateCountBound] using cnot
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits, RSA.gateCountBoundAtCount,
      NativeRSA2048.model_gateCountBound_eq model .singleQubit,
      NativeRSA2048.gateCountBound] using singleQubit
  · have scalarEq :
        RSA.cycleDepthBoundAtCount N NativeRSA2048.rounds =
          NativeRSA2048.maximumCycleDepthBound := by
        change NativeCycles.Finite.batchDepthScalarBound N =
          NativeRSA2048.maximumCycleDepthBound
        exact NativeRSA2048.model_batchDepthScalarBound_eq model
    calc
      (sevenBatchCertificate base noQuantum specification).maximumCycleDepth
          (fun _ => 1) path ≤ RSA.cycleDepthBoundAtCount N NativeRSA2048.rounds :=
        cycleDepth
      _ = NativeRSA2048.maximumCycleDepthBound := scalarEq
      _ = 2_399_834_962_524_657_350 := rfl
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits,
      NativeRSA2048.model_classicalBitBound_eq model,
      NativeRSA2048.classicalBitBound] using residentBits
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits,
      NativeRSA2048.model_classicalBitBound_eq model,
      NativeRSA2048.classicalBitBound] using auxiliaryBits
  · simpa only [RSA.coordinateLimitsAtCount, coordinateLimits, RSA.classicalOperationBoundAtCount,
      NativeRSA2048.model_scalarClassicalOperationBound_eq model,
      NativeRSA2048.classicalOperationBound] using classicalOperations

/-- With no incoming classical storage, both complete memory coordinates fit in
132 decimal gigabytes (one gigabyte is 10^9 bytes). -/
public theorem algorithm_classicalMemory_emptyBase_le_132GB {N : Nat}
    (model : NativeRSA2048.FixedWidthModel N) (specification : Canonical.Input N)
    (path : (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.Path) :
    (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.peakResidentSpace
        path .classicalBits ≤ 132 * 8 * 10 ^ 9 ∧
    (algorithm (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires specification).run.code.peakAuxiliarySpace
        path .classicalBits ≤ 132 * 8 * 10 ^ 9 := by
  rcases algorithm_sevenCoordinates (RuntimeCtx.empty : RuntimeCtx .quantum)
      RuntimeCtx.runtimeCtx_empty_quantumWires model specification path with
    ⟨_, _, _, _, _, ⟨resident, auxiliary⟩, _⟩
  constructor
  · calc
      _ ≤ (RuntimeCtx.empty : RuntimeCtx .quantum).residentSpace .classicalBits +
          1_053_148_427_049 := resident
      _ ≤ 132 * 8 * 10 ^ 9 := by norm_num [RuntimeCtx.residentSpace_empty]
  · calc
      _ ≤ (RuntimeCtx.empty : RuntimeCtx .quantum).auxiliarySpace .classicalBits +
          1_053_148_427_049 := auxiliary
      _ ≤ 132 * 8 * 10 ^ 9 := by norm_num [RuntimeCtx.auxiliarySpace_empty]

/-- The original ordered uniform key distribution is followed by the named actual algorithm.
The input family may correlate the generated key with the incoming state and reference. -/
public def keygenOutput {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput .empty base Reference) : PMF (Nat × Nat × Option Nat) :=
  (QuantumAlg.RSA.RSAKeyGenBits NativeRSA2048.primeBits NativeRSA2048.keygenNonempty).bind
    fun pair => ((algorithm base noQuantum (inputOfKeyPair pair)).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

private theorem keygenOutput_eq {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput .empty base Reference) :
    keygenOutput base noQuantum inputs =
      NativeKeyGeneration.outputDistribution base noQuantum NativeRSA2048.primeBits
        NativeRSA2048.keygenNonempty NativeRSA2048.rounds inputs := rfl

/-- The actual uniform-key average reaches ninety-nine percent for every input/reference family. -/
public theorem success_ge_99 {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput .empty base Reference) :
    ENNReal.ofReal ((99 : Real) / 100) ≤
      (keygenOutput base noQuantum inputs).toOuterMeasure NativeKeyGeneration.successEvent := by
  rw [keygenOutput_eq]
  exact NativeRSA2048.Calibration.combinedSuccess_seven_ge_99.trans
    (NativeKeyGeneration.success_ge_rounds base noQuantum NativeRSA2048.primeBits
      NativeRSA2048.keygenNonempty NativeRSA2048.rounds inputs
        (by norm_num [QuantumAlg.RSA.GeneratorOrder.effectiveCutoffBits, NativeRSA2048.primeBits]))

/-- Every supported populated output is one of its generated primes, including exceptional keys. -/
public theorem keygenOutput_some_sound {Reference : Register}
    (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
      Execution.OracleInput .empty base Reference) {p q factor : Nat}
    (member : (p, q, some factor) ∈ (keygenOutput base noQuantum inputs).support) :
    factor = p ∨ factor = q := by
  rw [keygenOutput_eq] at member
  exact NativeKeyGeneration.outputDistribution_some_sound base noQuantum
    NativeRSA2048.primeBits NativeRSA2048.keygenNonempty NativeRSA2048.rounds inputs member

/-- The registered fixed endpoint supplies the completed-cycle certificate for every input,
binding its seven numerical coordinates to that witness for every original exact-width key,
the complete independent resource budget, and the original ninety-nine-percent
uniform-key guarantee for all incoming reference extensions. -/
public theorem main {N : Nat} (model : NativeRSA2048.FixedKeyModel N) :
    ∃ cycles : ∀ (N : Nat) (specification : Canonical.Input N),
        Algorithm.CycleSolves (algorithm base noQuantum specification)
          (sevenBatchProblem base noQuantum specification),
      Algorithm.Solves (algorithm base noQuantum model.1.input)
          (problem base noQuantum model) ∧
        (∀ (N : Nat) (_widthModel : NativeRSA2048.FixedWidthModel N)
          (specification : Canonical.Input N)
          (path : (algorithm base noQuantum specification).run.code.Path),
          SevenCoordinateBounds base noQuantum specification (cycles N specification) path) ∧
        (∀ (N : Nat) (_widthModel : NativeRSA2048.FixedWidthModel N)
          (specification : Canonical.Input N), ResourceBounds base noQuantum specification) ∧
        ∀ (Reference : Register)
          (inputs : QuantumAlg.RSA.RSAKeyPairBits NativeRSA2048.primeBits →
            Execution.OracleInput .empty base Reference),
          ENNReal.ofReal ((99 : Real) / 100) ≤
            (keygenOutput base noQuantum inputs).toOuterMeasure
              NativeKeyGeneration.successEvent :=
  ⟨fun _ specification => sevenBatchCertificate base noQuantum specification,
    algorithm_solves base noQuantum model,
    fun _ widthModel specification path =>
      algorithm_sevenCoordinates base noQuantum widthModel specification path,
    fun _ widthModel specification =>
      algorithm_resourceBounds base noQuantum widthModel specification,
    fun _ inputs => success_ge_99 base noQuantum inputs⟩

end

end QuantumAlg.Factoring.RSA2048
