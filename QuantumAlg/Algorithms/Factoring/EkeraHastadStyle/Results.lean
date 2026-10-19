/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint.Time
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Statistics
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Restart
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.KeyAverage
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.PrimeAcceptance
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Context
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.SpaceCoordinates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Reuse.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.QuantumTime
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Same-run Ekerå–Håstad success and resource results

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
    (η : Real) :
    Algorithm (Native.Declared.model N) base
      (Finite.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  Finite.completedAlgorithm base noQuantum input (NativeFiniteRetry.Calibration.retryCount η)

/-- The completed-batch candidate on the same public modulus and calibrated
total count. Every positive batch pays its own pack and physical reset. -/
@[expose] public def completedAlgorithm {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    Algorithm (Native.Declared.model N) base
      (Finite.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount η))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  algorithm base noQuantum input η

/-- The ordinary public algorithm satisfies the all-input source, full-state,
restoration and resource contract of its own completed execution. -/
public lemma algorithm_solves {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    Algorithm.Solves (algorithm base noQuantum input η)
      (problem base noQuantum input η) :=
  Finite.completedAlgorithm_solves base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)

/-- The original ordered key law followed by the completed-batch candidate.
Each key is sampled once before executing the actual completed schedule. -/
public def completedKeygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (η : Real) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model pair.modulus).classicalOracles
        base Reference) : PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((completedAlgorithm base noQuantum (inputOfKeyPair pair) η).run.outputDistribution
      (Native.Declared.sourceEnvironment (inputOfKeyPair pair)) (inputs pair)).map
        fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The same eventual ordered-key target, evaluated on the completed physical
schedule and with key-dependent caller, service and reference inputs. -/
@[expose] public def CompletedAsymptoticKeygenSuccess
    (η : Real) : Prop :=
  ∀ᶠ bitWidth in Filter.atTop,
    ∀ nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth),
      RSA.GeneratorOrder.effectiveCutoffBits ≤ bitWidth →
      ∀ (Reference : Register)
        (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
          Execution.OracleInput (Native.Declared.model pair.modulus).classicalOracles
            base Reference),
        ENNReal.ofReal (1 - η) ≤
          (completedKeygenOutput base noQuantum bitWidth nonempty η inputs).toOuterMeasure
            {triple | ∃ factor, triple.2.2 = some factor ∧
              (factor = triple.1 ∨ factor = triple.2.1)}

/-- Moving physical cleanup between batches leaves the original eventual
uniform ordered-key success theorem true of the completed candidate. -/
public lemma completedAsymptoticKeygenSuccess (η : Real)
    (etaPositive : 0 < η) :
    CompletedAsymptoticKeygenSuccess base noQuantum η := by
  filter_upwards [Finite.eventually_completedFinite_keygen_success_ge_target
    base noQuantum η etaPositive] with bitWidth succeeds
  intro nonempty effective reference inputs
  exact succeeds nonempty effective inputs

/-- The ordinary key-generation observable evaluates the same completed
algorithm that is named by the public `algorithm` declaration. -/
public def keygenOutput (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (η : Real) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model pair.modulus).classicalOracles
        base Reference) : PMF (Nat × Nat × Option Nat) :=
  completedKeygenOutput base noQuantum bitWidth nonempty η inputs

/-- The observable samples the original ordered key once and then executes
this same public algorithm on the corresponding caller/service/reference input. -/
public lemma completedKeygenOutput_eq_algorithm (bitWidth : Nat)
    (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (η : Real) {Reference : Register}
    (inputs : (pair : RSA.RSAKeyPairBits bitWidth) →
      Execution.OracleInput (Native.Declared.model pair.modulus).classicalOracles
        base Reference) :
    completedKeygenOutput base noQuantum bitWidth nonempty η inputs =
      (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
        ((algorithm base noQuantum (inputOfKeyPair pair) η).run.outputDistribution
          (Native.Declared.sourceEnvironment (inputOfKeyPair pair)) (inputs pair)).map fun output =>
            (pair.p, pair.q, NativeRetrySelection.decodeFactor output) := by rfl

/-- The ordinary public average target refers to the completed execution. -/
@[expose] public def AsymptoticKeygenSuccess (η : Real) : Prop :=
  CompletedAsymptoticKeygenSuccess base noQuantum η

/-- The ordinary public key average retains the original one-time exception
bound on the same completed execution used by `main`. -/
public lemma asymptoticKeygenSuccess (η : Real)
    (etaPositive : 0 < η) :
    AsymptoticKeygenSuccess base noQuantum η :=
  completedAsymptoticKeygenSuccess base noQuantum η etaPositive

/-- On the original good-key domain, the completed all-input source law still
meets the real conditional half-target on its actual result distribution. -/
public lemma completedAlgorithm_goodSuccess_ge_halfTarget {N : Nat}
    (good : Canonical.GoodKeyModel N) (η : Real)
    (etaPositive : 0 < η) {Reference : Register}
    (original : Execution.OracleInput
      (Native.Declared.model N).classicalOracles base Reference) :
    1 - ENNReal.ofReal (η / 2) ≤
      ((completedAlgorithm base noQuantum good.input η).run.outputDistribution
        (Native.Declared.sourceEnvironment good.input) original).toOuterMeasure
          {output | output ≠ CShape.Value.optionNone} := by
  exact (tsub_le_tsub_left
    (NativeFiniteRetry.Calibration.retryBatchFailure_le_halfTarget
      good.effective η etaPositive) 1).trans
    (Finite.completedAlgorithm_successProbability_ge
      base noQuantum good (NativeFiniteRetry.Calibration.retryCount η) original)

/-- The same ordinary public algorithm reaches the calibrated conditional target
for precisely the two declared primes under the original good-key witness. -/
public lemma algorithm_primeAcceptance_ge_halfTarget {N : Nat}
    (good : Canonical.GoodKeyModel N) (η : Real)
    (etaPositive : 0 < η) {Reference : Register}
    (original : Execution.OracleInput
      (Native.Declared.model N).classicalOracles base Reference) :
    1 - ENNReal.ofReal (η / 2) ≤
      ((algorithm base noQuantum good.input η).run.outputDistribution
        (Native.Declared.sourceEnvironment good.input) original).toOuterMeasure
          {output | NativeRetrySelection.decodeFactor output ∈ NativeBatchSuccess.accepts good} :=
  Finite.completedAlgorithm_primeAcceptance_ge_halfTarget
    base noQuantum good η etaPositive original

/-- Chronological depth charges every completed batch, including its recovery
and cleanup, under the supplied event duration. -/
public lemma algorithm_wholeRunDepth_le {N : Nat} (input : Canonical.Input N)
    (η : Real)
    (duration : Resource.Event (Native.Declared.model N) → Nat)
    (path : (algorithm base noQuantum input η).run.code.Path) :
    (algorithm base noQuantum input η).run.code.depth duration path ≤
      NativeFiniteRetry.Calibration.retryCount η *
        Finite.Cleanup.twoCompletedMaximumBatchBudget N duration := by
  exact Finite.completedAlgorithm_wholeRunDepth_le
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η) duration path

/-- The same real-target algorithm charges every sequential member and every reset.
Classical recovery and packing retain their event counts and have zero quantum duration. -/
public lemma algorithm_wholeRunQuantumTime_le {N : Nat} (input : Canonical.Input N)
    (η : Real) (path : (algorithm base noQuantum input η).run.code.Path) :
    (algorithm base noQuantum input η).run.code.quantumTime path ≤
      16 * NativeFiniteRetry.Calibration.retryCount η *
          Native.Declared.memberQuantumTimeBound N +
        (17 * NativeFiniteRetry.Calibration.retryCount η - 1) *
          Native.Declared.resetQuantumTime N :=
  Finite.completedAlgorithm_wholeRunQuantumTime_le
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η) path

/-- The public problem fixes the independent whole-run formula on every real target.
This equality also covers the zero-count extension of the total calibration function. -/
public lemma problem_quantumTimeLimit {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    (problem base noQuantum input η).quantumTimeLimit =
      16 * NativeFiniteRetry.Calibration.retryCount η *
          Native.Declared.memberQuantumTimeBound N +
        (17 * NativeFiniteRetry.Calibration.retryCount η - 1) *
          Native.Declared.resetQuantumTime N := by
  change (Finite.completedAllProblem base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)).quantumTimeLimit = _
  generalize NativeFiniteRetry.Calibration.retryCount η = count
  cases count with
  | zero =>
      simp only [Finite.completedAllProblem, Finite.AllKeys.problem,
        Finite.Cleanup.durationBudget, Nat.mul_zero, Nat.zero_mul,
        Nat.zero_sub, Nat.zero_add]
  | succ laterCount =>
      change Finite.Cleanup.completedQuantumTimeBudget N laterCount =
        16 * (laterCount + 1) * Native.Declared.memberQuantumTimeBound N +
          (17 * (laterCount + 1) - 1) * Native.Declared.resetQuantumTime N
      unfold Finite.Cleanup.completedQuantumTimeBudget
      rw [show 17 * (laterCount + 1) - 1 = 16 + 17 * laterCount by omega]

private lemma fourierQuantumTime_mono {left right : Nat}
    (positive : 2 ≤ left) (ordered : left ≤ right) :
    Native.Declared.nativeFourierQuantumTimeBound left ≤
      Native.Declared.nativeFourierQuantumTimeBound right := by
  have leftNonzero : left / 2 ≠ 0 := by omega
  have rightNonzero : right / 2 ≠ 0 := by omega
  simp only [Native.Declared.nativeFourierQuantumTimeBound,
    if_neg leftNonzero, if_neg rightNonzero]
  exact Nat.add_le_add (Nat.add_le_add ordered
    (Nat.mul_le_mul_left 5 (Nat.choose_le_choose 2 ordered))) le_rfl

private lemma twice_choose_successor (width : Nat) :
    2 * (width + 1).choose 2 = width * (width + 1) := by
  induction width with
  | zero => norm_num
  | succ width previous =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith

private lemma completeTime_polynomial (count width : Nat) :
    16 * count * (width + 6 + 5 * (width + 1).choose 2) + (17 * count - 1) =
      count * (40 * width ^ 2 + 56 * width + 113) - 1 := by
  have coefficient :
      16 * (width + 6 + 5 * (width + 1).choose 2) + 17 =
        40 * width ^ 2 + 56 * width + 113 := by
    have triangle := twice_choose_successor width
    nlinarith
  have joined :
      16 * count * (width + 6 + 5 * (width + 1).choose 2) + 17 * count =
        count * (40 * width ^ 2 + 56 * width + 113) := by
    rw [← coefficient]
    ring
  cases count with
  | zero => simp
  | succ count => omega

/-- The independent whole-run time has a closed polynomial on the original same-bit keys.
Natural subtraction also gives zero for the total calibration's zero-count extension. -/
public lemma problem_quantumTimeLimit_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (large : 2 ≤ n) (input : Canonical.Input pair.modulus) (η : Real) :
    (problem base noQuantum input η).quantumTimeLimit =
      NativeFiniteRetry.Calibration.retryCount η *
        (40 * (n + (n + 2) / 2) ^ 2 + 56 * (n + (n + 2) / 2) + 113) - 1 := by
  have positive : 1 ≤ n := by omega
  have tradeoffLarge : 2 ≤ (n + 2) / 2 := by omega
  have firstNonzero : (n + (n + 2) / 2 + 1) / 2 ≠ 0 := by omega
  have member : Native.Declared.memberQuantumTimeBound pair.modulus =
      n + (n + 2) / 2 + 6 + 5 * (n + (n + 2) / 2 + 1).choose 2 := by
    rw [Native.Declared.memberQuantumTimeBound, tradeoffBits_sameBit pair positive,
      shortLogBits_sameBit pair positive]
    change 2 + max
      (Native.Declared.nativeFourierQuantumTimeBound ((n + 2) / 2 + (n + 1)))
      (Native.Declared.nativeFourierQuantumTimeBound ((n + 2) / 2)) = _
    rw [show (n + 2) / 2 + (n + 1) = n + (n + 2) / 2 + 1 by omega]
    rw [max_eq_left (fourierQuantumTime_mono tradeoffLarge (by omega))]
    simp only [Native.Declared.nativeFourierQuantumTimeBound, if_neg firstNonzero]
    omega
  have reset : Native.Declared.resetQuantumTime pair.modulus = 1 := by
    simp only [Native.Declared.resetQuantumTime,
      Native.nativeOracle_qubitCount_sameBit pair positive, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, if_false]
  rw [problem_quantumTimeLimit, member, reset, Nat.mul_one]
  exact completeTime_polynomial (NativeFiniteRetry.Calibration.retryCount η) _

/-- Every actual path of the same public algorithm obeys the closed same-bit time bound. -/
public lemma algorithm_wholeRunQuantumTime_sameBit_le {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (large : 2 ≤ n) (input : Canonical.Input pair.modulus)
    (η : Real) (path : (algorithm base noQuantum input η).run.code.Path) :
    (algorithm base noQuantum input η).run.code.quantumTime path ≤
      NativeFiniteRetry.Calibration.retryCount η *
        (40 * (n + (n + 2) / 2) ^ 2 + 56 * (n + (n + 2) / 2) + 113) - 1 := by
  rw [← problem_quantumTimeLimit_sameBit base noQuantum pair large input η,
    problem_quantumTimeLimit]
  exact algorithm_wholeRunQuantumTime_le base noQuantum input η path

/-- The ordinary public completed algorithm lists every original caller key,
retained result and owned bank wire at the final output. -/
public lemma algorithm_output_listing {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    (algorithm base noQuantum input η).run.output.listing =
      (Finite.context base noQuantum N (NativeFiniteRetry.Calibration.retryCount η)).keys :=
  Finite.completedAlgorithm_output_listing base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)

/-- The ordinary public completed algorithm retains the original single-bank
same-bit qubit width on every actual path. -/
public lemma algorithm_resident_qubits_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (etaPositive : 0 < η) (etaLessOne : η < 1)
    (path : (algorithm base noQuantum input η).run.code.Path) :
    (algorithm base noQuantum input η).run.code.peakResidentSpace path
      (.quantumSystems 2) ≤ 3 * n + 2 * ((n + 2) / 2) + 1 := by
  have bounded := Finite.completedAlgorithm_peakResidentSpace_le
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η) path
  have qubits :
    Finite.Cleanup.qubitBound pair.modulus (NativeFiniteRetry.Calibration.retryCount η) =
      3 * n + 2 * ((n + 2) / 2) + 1 := by
    have countPositive :=
      NativeFiniteRetry.Calibration.realRetryCount_pos η etaPositive etaLessOne
    obtain ⟨count, countEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt countPositive)
    change Finite.Cleanup.qubitBound pair.modulus
      (NativeFiniteRetry.Calibration.retryCount η) = _
    rw [countEq]
    exact Finite.Cleanup.declaredCleanup_qubitBound_sameBit pair positive count
  have caller : base.residentSpace (.quantumSystems 2) = 0 := by
    simp [RuntimeCtx.residentSpace_quantumSystems, RuntimeCtx.quantumLayout,
      dimensionCount_ofWires, noQuantum]
  have quantumSpace :
      Finite.additionalSpace pair.modulus (NativeFiniteRetry.Calibration.retryCount η)
        (.quantumSystems 2) =
        Finite.Cleanup.qubitBound pair.modulus (NativeFiniteRetry.Calibration.retryCount η) := by
    simpa using Finite.Cleanup.declaredCleanup_additionalSpace_quantum
      pair.modulus (NativeFiniteRetry.Calibration.retryCount η) 2
  have allowance :
      (Finite.additionalSpace pair.modulus (NativeFiniteRetry.Calibration.retryCount η) +
        base.residentSpace) (.quantumSystems 2) =
          Finite.Cleanup.qubitBound pair.modulus (NativeFiniteRetry.Calibration.retryCount η) +
            base.residentSpace (.quantumSystems 2) :=
    congrArg (· + base.residentSpace (.quantumSystems 2)) quantumSpace
  exact (bounded (.quantumSystems 2)).trans_eq
    (allowance.trans (by rw [qubits, caller, Nat.add_zero]))

/-- The ordinary completed problem has the same fixed resident classical
capacity at zero and positive batch counts, in addition to the caller's own. -/
public lemma problem_resident_classicalBits {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    (problem base noQuantum input η).resources.resident .classicalBits =
      Finite.Cleanup.classicalBitBound N (NativeFiniteRetry.Calibration.retryCount η) +
        base.residentSpace .classicalBits := by
  have space := Finite.completedAllProblem_residentSpace base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)
  change (Finite.completedAllProblem base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)).resources.resident .classicalBits = _
  rw [space]
  exact congrArg (· + base.residentSpace .classicalBits)
    (Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- Every actual path of the ordinary completed algorithm fits the complete
classical resident allowance, including recovery, selection and retained output. -/
public lemma algorithm_resident_classicalBits_le {N : Nat}
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm base noQuantum input η).run.code.Path) :
    (algorithm base noQuantum input η).run.code.peakResidentSpace path
      .classicalBits ≤
        Finite.Cleanup.classicalBitBound N (NativeFiniteRetry.Calibration.retryCount η) +
          base.residentSpace .classicalBits := by
  have bounded := Finite.completedAlgorithm_peakResidentSpace_le
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η) path
  have bits := Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits
    N (NativeFiniteRetry.Calibration.retryCount η)
  exact (bounded .classicalBits).trans_eq (congrArg
    (· + base.residentSpace .classicalBits) bits)

/-- The caller's auxiliary classical role remains distinct on the ordinary
completed problem's same fixed storage allowance. -/
public lemma problem_auxiliary_classicalBits {N : Nat} (input : Canonical.Input N)
    (η : Real) :
    (problem base noQuantum input η).resources.auxiliary .classicalBits =
      Finite.Cleanup.classicalBitBound N (NativeFiniteRetry.Calibration.retryCount η) +
        base.auxiliarySpace .classicalBits := by
  have space := Finite.completedAllProblem_auxiliarySpace base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)
  change (Finite.completedAllProblem base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)).resources.auxiliary .classicalBits = _
  rw [space]
  exact congrArg (· + base.auxiliarySpace .classicalBits)
    (Finite.Cleanup.declaredCleanup_additionalSpace_classicalBits N
      (NativeFiniteRetry.Calibration.retryCount η))

/-- Every quantum dimension of the resident allowance is explicit: the
algorithm adds only its original qubit bank to the caller's resident role. -/
public lemma problem_resident_quantumSystems {N : Nat} (input : Canonical.Input N)
    (η : Real) (dimension : ℕ+) :
    (problem base noQuantum input η).resources.resident (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then
        Finite.Cleanup.qubitBound N (NativeFiniteRetry.Calibration.retryCount η) else 0) +
          base.residentSpace (.quantumSystems dimension) := by
  have space := Finite.completedAllProblem_residentSpace base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)
  change (Finite.completedAllProblem base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)).resources.resident
      (.quantumSystems dimension) = _
  rw [space]
  exact congrArg (· + base.residentSpace (.quantumSystems dimension))
    (Finite.Cleanup.declaredCleanup_additionalSpace_quantum N
      (NativeFiniteRetry.Calibration.retryCount η) dimension)

/-- The same dimension-wise allowance retains the caller's auxiliary role
separately, without treating it as additional resident storage. -/
public lemma problem_auxiliary_quantumSystems {N : Nat} (input : Canonical.Input N)
    (η : Real) (dimension : ℕ+) :
    (problem base noQuantum input η).resources.auxiliary (.quantumSystems dimension) =
      (if (2 : ℕ+) = dimension then
        Finite.Cleanup.qubitBound N (NativeFiniteRetry.Calibration.retryCount η) else 0) +
          base.auxiliarySpace (.quantumSystems dimension) := by
  have space := Finite.completedAllProblem_auxiliarySpace base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)
  change (Finite.completedAllProblem base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η)).resources.auxiliary
      (.quantumSystems dimension) = _
  rw [space]
  exact congrArg (· + base.auxiliarySpace (.quantumSystems dimension))
    (Finite.Cleanup.declaredCleanup_additionalSpace_quantum N
      (NativeFiniteRetry.Calibration.retryCount η) dimension)

end

end QuantumAlg.Factoring.EkeraHastadStyle
