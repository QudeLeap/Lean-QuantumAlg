/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.KeyGeneration
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.SpaceCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.KeyGeneration
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.EventCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Retry.Finite.Counts.SameBit

/-!
# Ekerå–Håstad factoring with the actual original-width oracle bank

One internally prepared bank carries the original two exponent registers and
modulus-width XOR target. Sixteen actual samples share each retained parameter;
later samples reset the same bank. Actual recovery and first-accepted selection
operate on the stored observations. The external reference and every borrowed
caller entry are preserved jointly. Key generation is a theorem-side average
of this same execution, outside the circuit resource ledger.

The RSA reduction is [EH17, source.tex:878-966]. The source quantum state and
measurement law are [E23, arxiv-v5.tex:218-299]; lattice post-processing is
[E23, arxiv-v5.tex:329-355]. The exact named query and QFT coordinates survive
bank reuse. Actual resets, result packing and reused classical storage have
separate complete native allowances, not the former oracle-only depth ledger.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle

open Canonical Canonical.OracleModel

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Complete conditional factoring with the original sealed XOR oracle.

**Input.** The executable data are the public modulus N and rational target
0 < eta <= 1. Two distinct odd equal-width primes, exact doubled product width,
the effective-width bound and the original good-key condition certify the
result. Every normalized caller classical state and finite external reference
is admitted. The caller supplies no quantum wires.
**Output.** An actually stored optional factor word, accepted when it names one
of the two original primes. Every live cell and quantum wire is listed. Owned
final quantum state is unrestricted; borrowed restoration is mandatory.
**Resource budget.** The original count is
k = max(1, ceil(log(2/eta)/log(256/147))). For ell = floor((n+2)/2) and
r = n+1+ell, the same actual paths have 16k queries, 32k(n+1+2ell) Hadamards,
8k(r(r-1)+ell(ell-1)) controlled phases, and 16k(floor(r/2)+floor(ell/2)) swaps.
One bank has 3n+2ell+1 qubits. Literal classical operations are bounded by
2^54 k n^3 + 2. Additional classical capacity is
21M+18d+4+max(9M+14,A+8M+2), with modulus width M, observation width d and
actual complete recovery allocation A; the caller's original capacities remain
counted. The independent native pool and arbitrary-duration depth budget charge
all actual preparations, measurements, resets, packs, recovery and selection.
The gate/query clock charges reset corrections and gives an upper bound.
**Success.** Conditional success is at least 1-eta/2. The main theorem also
proves eventual success at least 1-eta over the original uniform ordered key
law, charging its exceptional mass once outside the retry power.
**Source.** [EH17, source.tex:878-966]; [E23, arxiv-v5.tex:218-299,329-355].
-/
@[expose] public def problem {N : Nat} (model : Canonical.GoodKeyModel N)
    (budget : FailureBudget) :
    Problem .quantum base (Native.outputContext base noQuantum N (Native.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Native.problem base noQuantum model budget

/-- The unique public candidate executes the original-bank finite program on public data only. -/
public def algorithm {N : Nat} (input : Canonical.Input N) (budget : FailureBudget) :
    Algorithm .quantum base
      (Native.outputContext base noQuantum N (Native.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) where
  run := Native.Retry.Finite.run base noQuantum N input (Native.calibratedCount budget)

/-- All conditional probability, state, borrowed-resource and actual resource gates hold. -/
public theorem algorithm_solves {N : Nat} (model : Canonical.GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
      (problem base noQuantum model budget) :=
  Native.nativeOracle_algorithm_solves base noQuantum model budget wellFormed

/-- The same actual public candidate is observed inside each original uniform-key branch. -/
public def keygenOutput (bitWidth : Nat) (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference) :
    PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((algorithm base noQuantum (inputOfKeyPair pair) budget).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The full original target permits initial caller/reference states depending on the key. -/
@[expose] public def AsymptoticKeygenSuccess (budget : FailureBudget) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
      RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : RSA.RSAKeyPairBits bitWidth → Execution.Input base Reference),
        FailureBudget.successThreshold budget ≤
          (keygenOutput base noQuantum bitWidth nonempty budget inputs).toOuterMeasure
            {triple | ∃ factor, triple.2.2 = some factor ∧
              (factor = triple.1 ∨ factor = triple.2.1)}

/-- The original one-time key exception and conditional half-target give eventual full success. -/
public theorem asymptoticKeygenSuccess (budget : FailureBudget)
    (wellFormed : budget.WellFormed) : AsymptoticKeygenSuccess base noQuantum budget := by
  filter_upwards [Native.eventually_nativeOracle_keygen_success_ge_target
    base noQuantum budget wellFormed] with bitWidth succeeds
  intro nonempty effective reference inputs
  exact succeeds nonempty effective inputs

/-- Original-bank factoring combines the complete actual conditional contract and key average. -/
public theorem main {N : Nat} (model : Canonical.GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.Solves (algorithm base noQuantum model.input budget)
        (problem base noQuantum model budget) ∧
      AsymptoticKeygenSuccess base noQuantum budget :=
  ⟨algorithm_solves base noQuantum model budget wellFormed,
    asymptoticKeygenSuccess base noQuantum budget wellFormed⟩

/-- Exact queries on every actual path, including all paid resets and classical processing. -/
theorem algorithm_query_count {N : Nat} (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    ResourcePool.count (ShortDLP.oracleEvent N (Native.parameters N))
      ((algorithm base noQuantum input budget).run.code.resourcePool path) =
        16 * Native.calibratedCount budget :=
  Native.Retry.Finite.nativeOracle_finiteRetry_query_count base noQuantum N input
    (Native.calibratedCount budget) path

/-- The original exact Hadamard formula observes the same actual paths. -/
theorem algorithm_hadamard_count_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Canonical.Input pair.modulus) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    ResourcePool.count WalshHadamard.hadamardEvent
      ((algorithm base noQuantum input budget).run.code.resourcePool path) =
        32 * Native.calibratedCount budget * (n + 1 + 2 * ((n + 2) / 2)) :=
  Native.Retry.Finite.nativeOracle_finiteRetry_hadamard_count_sameBit base noQuantum pair
    positive input (Native.calibratedCount budget) path

/-- Both original inverse QFTs retain the exact controlled-phase coordinate. -/
theorem algorithm_controlledPhase_count_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Canonical.Input pair.modulus) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    ResourcePool.count qftControlledPhaseEvent
      ((algorithm base noQuantum input budget).run.code.resourcePool path) =
        8 * Native.calibratedCount budget *
          ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
            ((n + 2) / 2) * ((n + 2) / 2 - 1)) :=
  Native.Retry.Finite.nativeOracle_finiteRetry_controlledPhase_count_sameBit base noQuantum pair
    positive input (Native.calibratedCount budget) path

/-- Both original inverse QFTs retain their exact swap coordinate. -/
theorem algorithm_swap_count_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Canonical.Input pair.modulus) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    ResourcePool.count qftSwapEvent
      ((algorithm base noQuantum input budget).run.code.resourcePool path) =
        16 * Native.calibratedCount budget *
          ((n + 1 + (n + 2) / 2) / 2 + ((n + 2) / 2) / 2) :=
  Native.Retry.Finite.nativeOracle_finiteRetry_swap_count_sameBit base noQuantum pair positive
    input (Native.calibratedCount budget) path

/-- The original cubic ceiling covers actual typed classical instructions, including both packs. -/
theorem algorithm_classicalOperation_sameBit_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n) (input : Canonical.Input pair.modulus)
    (budget : FailureBudget) (path : (algorithm base noQuantum input budget).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm base noQuantum input budget).run.code.resourcePool path) ≤
        2 ^ 54 * Native.calibratedCount budget * n ^ 3 + 2 :=
  Native.Retry.Finite.nativeOracle_finiteRetry_classicalOperation_sameBit_le_cubic
    base noQuantum pair positive input (Native.calibratedCount budget) path

/-- The public resident allowance is the independent fixed reusable classical capacity. -/
theorem problem_resident_classicalBits {N : Nat} (model : Canonical.GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.resident .classicalBits =
      Native.Retry.Finite.classicalBitBound N (Native.calibratedCount budget) +
        base.residentSpace .classicalBits :=
  congrArg (· + base.residentSpace .classicalBits)
    (Native.Retry.Finite.nativeOracle_finiteRetry_additionalSpace_classicalBits N
      (Native.calibratedCount budget))

/-- The caller's auxiliary role is preserved separately from total resident capacity. -/
theorem problem_auxiliary_classicalBits {N : Nat} (model : Canonical.GoodKeyModel N)
    (budget : FailureBudget) :
    (problem base noQuantum model budget).resources.auxiliary .classicalBits =
      Native.Retry.Finite.classicalBitBound N (Native.calibratedCount budget) +
        base.auxiliarySpace .classicalBits :=
  congrArg (· + base.auxiliarySpace .classicalBits)
    (Native.Retry.Finite.nativeOracle_finiteRetry_additionalSpace_classicalBits N
      (Native.calibratedCount budget))

/-- The actual reused bank has the original same-bit width on every path. -/
theorem algorithm_resident_qubits_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) (input : Canonical.Input pair.modulus) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    (algorithm base noQuantum input budget).run.code.peakResidentSpace path (.quantumSystems 2) ≤
      3 * n + 2 * ((n + 2) / 2) + 1 := by
  have bounded := Native.Retry.Finite.nativeOracle_finiteRetry_resident_quantum_le
    base noQuantum pair.modulus input (Native.calibratedCount budget) 2 path
  have qubits : Native.Retry.Finite.qubitBound pair.modulus (Native.calibratedCount budget) =
      3 * n + 2 * ((n + 2) / 2) + 1 := by
    have countPositive := NativeFiniteRetry.Calibration.retryCount_pos budget
    obtain ⟨count, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countPositive)
    change Native.Retry.Finite.qubitBound pair.modulus
      (NativeFiniteRetry.Calibration.retryCount budget) = _
    rw [countEq]
    exact Native.Retry.Finite.nativeOracle_finiteRetry_qubitBound_sameBit pair positive count
  have caller : base.residentSpace (.quantumSystems 2) = 0 := by
    simp [RuntimeCtx.residentSpace_quantumSystems, RuntimeCtx.quantumLayout,
      dimensionCount_ofWires, noQuantum]
  exact bounded.trans_eq (by simp only [ite_true, qubits, caller, Nat.add_zero])

/-- Every original caller key and all actual retained results and wires occur in the output. -/
theorem algorithm_output_listing {N : Nat} (input : Canonical.Input N) (budget : FailureBudget) :
    (algorithm base noQuantum input budget).run.output.listing =
      (Native.outputContext base noQuantum N (Native.calibratedCount budget)).keys :=
  Native.nativeOracle_finiteAlgorithm_output_listing base noQuantum input
    (Native.calibratedCount budget)

/-- The actual arbitrary-duration critical path is bounded with every reset correction charged. -/
theorem algorithm_depth_le {N : Nat} (input : Canonical.Input N) (budget : FailureBudget)
    (duration : Resource.Event .quantum → Nat)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    (algorithm base noQuantum input budget).run.code.depth duration path ≤
      Native.Retry.Finite.durationBudget N duration (Native.calibratedCount budget) := by
  have bounded := Native.Retry.Finite.nativeOracle_finiteRetry_depth_le
    base noQuantum N input (Native.calibratedCount budget) duration
  rw [← Native.Retry.Finite.nativeOracle_finiteRetry_run_code] at bounded
  exact bounded path

end

end QuantumAlg.Factoring.EkeraHastadStyle
