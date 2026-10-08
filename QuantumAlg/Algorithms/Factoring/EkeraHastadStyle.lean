/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint.Cycle
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Statistics
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint.Cycle
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.KeyAverage
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.PrimeAcceptance
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates

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
[E23, arxiv-v5.tex:329-355]. The exact named query and QFT construction observations survive
bank reuse. Actual resets, result packing and reused classical storage have
separate complete native allowances, not the former oracle-only depth ledger.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle

open Canonical Canonical.OracleModel

open Native.Declared.Retry

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The ordinary public algorithm runs the independently completed batch
schedule on the original public modulus and calibrated total count. -/
@[expose] public def algorithm {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm (Native.Declared.model input) base
      (Finite.context base noQuantum N (Finite.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Finite.completedAlgorithm base noQuantum input (Finite.calibratedCount budget)

/-- The completed-batch candidate on the same public modulus and calibrated
total count. Every positive batch pays its own pack and physical reset. -/
@[expose] public def completedAlgorithm {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm (Native.Declared.model input) base
      (Finite.context base noQuantum N (Finite.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  algorithm base noQuantum input budget

/-- Independent all-input source outcome and complete-cycle plan for the
completed candidate at the public calibrated batch count. -/
@[expose] public def completedCycleProblem {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget)
    (duration : Resource.Event (Native.Declared.model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    CycleProblem (Native.Declared.model input) base
      (Finite.context base noQuantum N (Finite.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Finite.completedCycleProblem base noQuantum input duration unitQueries
    (Finite.calibratedCount budget)

/-- The named completed candidate satisfies its all-input finite source law,
full output state, borrowed and native budgets, and independently specified
actual batch-by-batch cycle schedule. -/
public def completedAlgorithmCycleSolves {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget)
    (duration : Resource.Event (Native.Declared.model input) → Nat)
    (unitQueries : ∀ coordinate, duration (.oracle coordinate) = 1) :
    Algorithm.CycleSolves (completedAlgorithm base noQuantum input budget)
      (completedCycleProblem base noQuantum input budget duration unitQueries) :=
  Finite.completedAlgorithmCycleSolves base noQuantum input
    (Finite.calibratedCount budget) duration unitQueries

/-- The ordinary public cycle problem uses the original gate/query clock and
the completed-batch all-input source law. -/
@[expose] public def cycleProblem {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :=
  completedCycleProblem base noQuantum input budget
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)

/-- The ordinary public problem is the independent outcome of that same
completed-batch cycle contract. -/
@[expose] public def problem {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    Problem (Native.Declared.model input) base
      (Finite.context base noQuantum N (Finite.calibratedCount budget))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  (cycleProblem base noQuantum input budget).outcome

/-- The ordinary public algorithm carries its own real completed-batch
schedule and all-input source/state/resource certificate. -/
public def algorithmCycleSolves {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm.CycleSolves (algorithm base noQuantum input budget)
      (cycleProblem base noQuantum input budget) :=
  completedAlgorithmCycleSolves base noQuantum input budget
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)

/-- The ordinary public algorithm satisfies the all-input source, full-state,
restoration and resource contract of its own completed execution. -/
public theorem algorithm_solves {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm.Solves (algorithm base noQuantum input budget)
      (problem base noQuantum input budget) :=
  (algorithmCycleSolves base noQuantum input budget).correctness

/-- The original ordered key law followed by the completed-batch candidate.
Each key is sampled once before executing the actual completed schedule. -/
public def completedKeygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model (inputOfKeyPair pair)).classicalOracles
        base Reference) : PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((completedAlgorithm base noQuantum (inputOfKeyPair pair) budget).run.outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The same eventual ordered-key target, evaluated on the completed physical
schedule and with key-dependent caller, service and reference inputs. -/
@[expose] public def CompletedAsymptoticKeygenSuccess
    (budget : FailureBudget) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
      RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
          Execution.OracleInput (Native.Declared.model (inputOfKeyPair pair)).classicalOracles
            base Reference),
        FailureBudget.successThreshold budget ≤
          (completedKeygenOutput base noQuantum bitWidth nonempty budget inputs).toOuterMeasure
            {triple | ∃ factor, triple.2.2 = some factor ∧
              (factor = triple.1 ∨ factor = triple.2.1)}

/-- Moving physical cleanup between batches leaves the original eventual
uniform ordered-key success theorem true of the completed candidate. -/
public theorem completedAsymptoticKeygenSuccess (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    CompletedAsymptoticKeygenSuccess base noQuantum budget := by
  filter_upwards [Finite.eventually_completedFinite_keygen_success_ge_target
    base noQuantum budget wellFormed] with bitWidth succeeds
  intro nonempty effective reference inputs
  exact succeeds nonempty effective inputs

/-- The ordinary key-generation observable evaluates the same completed
algorithm that is named by the public `algorithm` declaration. -/
public def keygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model (inputOfKeyPair pair)).classicalOracles
        base Reference) : PMF (Nat × Nat × Option Nat) :=
  completedKeygenOutput base noQuantum bitWidth nonempty budget inputs

/-- The observable samples the original ordered key once and then executes
this same public algorithm on the corresponding caller/service/reference input. -/
public theorem completedKeygenOutput_eq_algorithm (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (budget : FailureBudget) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model (inputOfKeyPair pair)).classicalOracles
        base Reference) :
    completedKeygenOutput base noQuantum bitWidth nonempty budget inputs =
      (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
        ((algorithm base noQuantum (inputOfKeyPair pair) budget).run.outputDistribution
          (inputs pair)).map fun output =>
            (pair.p, pair.q, NativeRetrySelection.decodeFactor output) := by rfl

/-- The ordinary public average target refers to the completed execution. -/
@[expose] public def AsymptoticKeygenSuccess (budget : FailureBudget) : Prop :=
  CompletedAsymptoticKeygenSuccess base noQuantum budget

/-- The ordinary public key average retains the original one-time exception
bound on the same completed execution used by `main`. -/
public theorem asymptoticKeygenSuccess (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    AsymptoticKeygenSuccess base noQuantum budget :=
  completedAsymptoticKeygenSuccess base noQuantum budget wellFormed

/-- On the original good-key domain, the completed all-input source law still
meets the rational conditional half-target on its actual result distribution. -/
public theorem completedAlgorithm_goodSuccess_ge_halfTarget {N : Nat}
    (good : Canonical.GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) {Reference : Register}
    (original : Execution.OracleInput
      (Native.Declared.model good.input).classicalOracles base Reference) :
    1 - ENNReal.ofReal (budget.value / 2) ≤
      ((completedAlgorithm base noQuantum good.input budget).run.outputDistribution
        original).toOuterMeasure
          {output | output ≠ CShape.Value.optionNone} := by
  exact (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
      good.effective budget wellFormed) 1).trans
    (Finite.completedAlgorithm_successProbability_ge
      base noQuantum good (Finite.calibratedCount budget) original)

/-- The same ordinary public algorithm reaches the calibrated conditional target
for precisely the two declared primes under the original good-key witness. -/
public theorem algorithm_primeAcceptance_ge_halfTarget {N : Nat}
    (good : Canonical.GoodKeyModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) {Reference : Register}
    (original : Execution.OracleInput
      (Native.Declared.model good.input).classicalOracles base Reference) :
    1 - ENNReal.ofReal (budget.value / 2) ≤
      ((algorithm base noQuantum good.input budget).run.outputDistribution
        original).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts good} :=
  Finite.completedAlgorithm_primeAcceptance_ge_halfTarget
    base noQuantum good budget wellFormed original

/-- The registered EH result now uses the actual independently completed
batch schedule. Its cycle contract supplies the all-input finite source law,
full state and resources; the original good-key and ordered-key success targets
hold on the very same completed execution. -/
public theorem main {N : Nat} (good : Canonical.GoodKeyModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∃ _cycles : Algorithm.CycleSolves
        (algorithm base noQuantum good.input budget)
        (cycleProblem base noQuantum good.input budget),
      (∀ (Reference : Register)
        (original : Execution.OracleInput
          (Native.Declared.model good.input).classicalOracles base Reference),
        1 - ENNReal.ofReal (budget.value / 2) ≤
          ((algorithm base noQuantum good.input budget).run.outputDistribution
            original).toOuterMeasure
              {output | output ≠ CShape.Value.optionNone}) ∧
      AsymptoticKeygenSuccess base noQuantum budget :=
  ⟨algorithmCycleSolves base noQuantum good.input budget,
    fun _ original => completedAlgorithm_goodSuccess_ge_halfTarget
      base noQuantum good budget wellFormed original,
    asymptoticKeygenSuccess base noQuantum budget wellFormed⟩

/-- The ordinary algorithm's maximum complete-cycle depth is bounded by an
independent maximum of the two completed-batch allowances, regardless of its
calibrated batch count. -/
public theorem algorithm_maximumCycleDepth_le {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    Algorithm.CycleSolves.maximumCycleDepth
      (algorithmCycleSolves base noQuantum input budget)
      (Finite.circuitDuration input) path ≤
        Finite.Cleanup.twoCompletedMaximumBatchBudget input
          (Finite.circuitDuration input) := by
  exact Finite.completedAlgorithm_maximumCycleDepth_le_positive
    base noQuantum input (Finite.calibratedCount budget)
      (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
        (NativeFiniteRetry.Calibration.retryCount_pos budget) path

/-- Chronological depth charges every completed batch separately. This bound
is distinct from the count-independent maximum complete-cycle allowance. -/
public theorem algorithm_wholeRunDepth_le {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget)
    (duration : Resource.Event (Native.Declared.model input) → Nat)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    (algorithm base noQuantum input budget).run.code.depth duration path ≤
      Finite.calibratedCount budget *
        Finite.Cleanup.twoCompletedMaximumBatchBudget input duration := by
  exact Finite.completedAlgorithm_wholeRunDepth_le
    base noQuantum input (Finite.calibratedCount budget) duration path

/-- The ordinary public completed algorithm lists every original caller key,
retained result and owned bank wire at the final output. -/
public theorem algorithm_output_listing {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    (algorithm base noQuantum input budget).run.output.listing =
      (Finite.context base noQuantum N (Finite.calibratedCount budget)).keys :=
  Finite.completedAlgorithm_output_listing base noQuantum input
    (Finite.calibratedCount budget)

/-- The ordinary public completed algorithm retains the original single-bank
same-bit qubit width on every actual path. -/
public theorem algorithm_resident_qubits_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    (algorithm base noQuantum input budget).run.code.peakResidentSpace path
      (.quantumSystems 2) ≤ 3 * n + 2 * ((n + 2) / 2) + 1 := by
  have bounded := Finite.completedAlgorithm_peakResidentSpace_le
    base noQuantum input (Finite.calibratedCount budget) path
  have qubits : Finite.Cleanup.qubitBound pair.modulus (Finite.calibratedCount budget) =
      3 * n + 2 * ((n + 2) / 2) + 1 := by
    have countPositive := NativeFiniteRetry.Calibration.retryCount_pos budget
    obtain ⟨count, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countPositive)
    change Finite.Cleanup.qubitBound pair.modulus
      (NativeFiniteRetry.Calibration.retryCount budget) = _
    rw [countEq]
    exact Finite.Cleanup.declaredCleanup_qubitBound_sameBit pair positive count
  have caller : base.residentSpace (.quantumSystems 2) = 0 := by
    simp [RuntimeCtx.residentSpace_quantumSystems, RuntimeCtx.quantumLayout,
      dimensionCount_ofWires, noQuantum]
  have quantumSpace :
      Finite.additionalSpace pair.modulus (Finite.calibratedCount budget)
        (.quantumSystems 2) =
        Finite.Cleanup.qubitBound pair.modulus (Finite.calibratedCount budget) := by
    simpa using Finite.Cleanup.declaredCleanup_additionalSpace_quantum
      pair.modulus (Finite.calibratedCount budget) 2
  have allowance :
      (Finite.additionalSpace pair.modulus (Finite.calibratedCount budget) +
        base.residentSpace) (.quantumSystems 2) =
          Finite.Cleanup.qubitBound pair.modulus (Finite.calibratedCount budget) +
            base.residentSpace (.quantumSystems 2) :=
    congrArg (· + base.residentSpace (.quantumSystems 2)) quantumSpace
  exact (bounded (.quantumSystems 2)).trans_eq
    (allowance.trans (by rw [qubits, caller, Nat.add_zero]))

/-- The ordinary completed problem has the same fixed resident classical
capacity at zero and positive batch counts, in addition to the caller's own. -/
public theorem problem_resident_classicalBits {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    (problem base noQuantum input budget).resources.resident .classicalBits =
      Finite.Cleanup.classicalBitBound N (Finite.calibratedCount budget) +
        base.residentSpace .classicalBits := by
  have space := Finite.completedAllProblem_residentSpace base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)
  change ((Finite.completedCycleProblem base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)).outcome).resources.resident .classicalBits = _
  rw [Finite.completedCycleProblem_outcome]
  rw [space]
  exact congrArg (· + base.residentSpace .classicalBits)
    (Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits N
      (Finite.calibratedCount budget))

/-- Every actual path of the ordinary completed algorithm fits the complete
classical resident allowance, including recovery, selection and retained output. -/
public theorem algorithm_resident_classicalBits_le {N : Nat}
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm base noQuantum input budget).run.code.Path) :
    (algorithm base noQuantum input budget).run.code.peakResidentSpace path
      .classicalBits ≤
        Finite.Cleanup.classicalBitBound N (Finite.calibratedCount budget) +
          base.residentSpace .classicalBits := by
  have bounded := Finite.completedAlgorithm_peakResidentSpace_le
    base noQuantum input (Finite.calibratedCount budget) path
  have bits := Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits
    N (Finite.calibratedCount budget)
  exact (bounded .classicalBits).trans_eq (congrArg
    (· + base.residentSpace .classicalBits) bits)

/-- The caller's auxiliary classical role remains distinct on the ordinary
completed problem's same fixed storage allowance. -/
public theorem problem_auxiliary_classicalBits {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) :
    (problem base noQuantum input budget).resources.auxiliary .classicalBits =
      Finite.Cleanup.classicalBitBound N (Finite.calibratedCount budget) +
        base.auxiliarySpace .classicalBits := by
  have space := Finite.completedAllProblem_auxiliarySpace base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)
  change ((Finite.completedCycleProblem base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)).outcome).resources.auxiliary .classicalBits = _
  rw [Finite.completedCycleProblem_outcome]
  rw [space]
  exact congrArg (· + base.auxiliarySpace .classicalBits)
    (Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits N
      (Finite.calibratedCount budget))

/-- Every quantum dimension of the resident allowance is explicit: the
algorithm adds only its original qubit bank to the caller's resident role. -/
public theorem problem_resident_quantumSystems {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) (dimension : ℕ+) :
    (problem base noQuantum input budget).resources.resident (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then
        Finite.Cleanup.qubitBound N (Finite.calibratedCount budget) else 0) +
          base.residentSpace (.quantumSystems dimension) := by
  have space := Finite.completedAllProblem_residentSpace base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)
  change ((Finite.completedCycleProblem base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)).outcome).resources.resident
      (.quantumSystems dimension) = _
  rw [Finite.completedCycleProblem_outcome, space]
  exact congrArg (· + base.residentSpace (.quantumSystems dimension))
    (Finite.Cleanup.declaredCleanup_additionalSpace_quantum N
      (Finite.calibratedCount budget) dimension)

/-- The same dimension-wise allowance retains the caller's auxiliary role
separately, without treating it as additional resident storage. -/
public theorem problem_auxiliary_quantumSystems {N : Nat} (input : Canonical.Input N)
    (budget : FailureBudget) (dimension : ℕ+) :
    (problem base noQuantum input budget).resources.auxiliary (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then
        Finite.Cleanup.qubitBound N (Finite.calibratedCount budget) else 0) +
          base.auxiliarySpace (.quantumSystems dimension) := by
  have space := Finite.completedAllProblem_auxiliarySpace base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)
  change ((Finite.completedCycleProblem base noQuantum input
    (Finite.circuitDuration input) (Finite.circuitDuration_oracle input)
    (Finite.calibratedCount budget)).outcome).resources.auxiliary
      (.quantumSystems dimension) = _
  rw [Finite.completedCycleProblem_outcome, space]
  exact congrArg (· + base.auxiliarySpace (.quantumSystems dimension))
    (Finite.Cleanup.declaredCleanup_additionalSpace_quantum N
      (Finite.calibratedCount budget) dimension)

end

end QuantumAlg.Factoring.EkeraHastadStyle
