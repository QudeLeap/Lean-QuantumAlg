/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Calibration

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint
public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.NativeCounts
public import QuantumAlg.Core.Base.Accounting.OracleWeight
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Specification
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Macros
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Cleanup.Counts.SameBit
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Costs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.ClassicalCounts
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.Endpoint.Accounting
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Retry.Finite.Completed.NativeCounts
import all QuantumAlg.Core.Base.Accounting.OracleWeight
import all QuantumAlg.Primitives.ShortDLP.Oracle.Declared

/-!
# Public resource observations of the completed original-width EH candidate

Native query occurrences, actual source-construction macro statistics and
literal classical-instruction ceilings all observe the same canonical run.
Macro statistics retain their expanded one-qubit/CNOT meaning and are never
presented as additional native coordinates.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle

open Canonical Canonical.OracleModel Native.Declared.Retry

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private abbrev declaredQueryEvent (N : Nat) :
    Resource.Event (Native.Declared.model N) :=
  .oracle .groupOperation

private lemma oracleWeight_eq_group_indicator (N : Nat)
    (event : Resource.Event (Native.Declared.model N)) :
    Resource.Event.oracleWeight event =
      if event = declaredQueryEvent N then 1 else 0 := by
  cases event with
  | classicalOperation _ => simp [Resource.Event.oracleWeight, declaredQueryEvent]
  | classicalQuery _ => simp [Resource.Event.oracleWeight, declaredQueryEvent]
  | gate _ => simp [Resource.Event.oracleWeight, declaredQueryEvent]
  | oracle coordinate =>
      change ShortDLP.DeclaredCoordinate at coordinate
      cases coordinate
      simp [Resource.Event.oracleWeight, declaredQueryEvent]
  | preparation _ => simp [Resource.Event.oracleWeight, declaredQueryEvent]
  | measurement _ => simp [Resource.Event.oracleWeight, declaredQueryEvent]

private lemma oracleCount_eq_groupQuery (N : Nat)
    (pool : ResourcePool (Native.Declared.model N)) :
    ResourcePool.weightedCount Resource.Event.oracleWeight pool =
      ResourcePool.count (declaredQueryEvent N) pool :=
  ResourcePool.weightedCount_eq_count_of_indicator _ _
    (oracleWeight_eq_group_indicator N) pool

/-- Exact granted-query count of the canonical completed-batch candidate,
including its classical zero-count branch and every paid reset. -/
public lemma completedAlgorithm_query_count {N : Nat} (input : Canonical.Input N)
    (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.oracleWeight
      ((Finite.completedAlgorithm base noQuantum input count).run.code.resourcePool path) =
        16 * count := by
  rw [oracleCount_eq_groupQuery N]
  exact Finite.completedAlgorithm_query_count base noQuantum input count path

/-- Source-construction statistics for the actual completed candidate. -/
public def completedAlgorithmSourceMacroCount {N : Nat} (input : Canonical.Input N)
    (count : Nat) (name : String)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) : Nat :=
  ResourcePool.weightedCount Resource.Event.oracleWeight
    ((Finite.completedAlgorithm base noQuantum input count).run.code.resourcePool path) *
      ShortDLP.DeclaredStage.sourceMacroCount N (Native.parameters N) name

/-- Actual completed paths retain the source Hadamard preparation and the two
inverse-QFT Hadamard layers at every one of their sixteen queries per batch. -/
public lemma completedAlgorithm_hadamard_count {N : Nat}
    (input : Canonical.Input N) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count "hadamard" path =
      32 * count *
        ((Native.parameters N).ell + (Native.parameters N).m +
          (Native.parameters N).ell) := by
  rw [completedAlgorithmSourceMacroCount, completedAlgorithm_query_count,
    ShortDLP.DeclaredStage.declaredStage_sourceMacroCount]
  simp [ShortDLP.firstBits]
  ring

/-- The actual completed path repeats the original controlled-phase source
construction once per declared member. -/
public lemma completedAlgorithm_controlledPhase_count {N : Nat}
    (input : Canonical.Input N) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count
      "controlled-phase" path =
        16 * count *
          (((Native.parameters N).ell + (Native.parameters N).m).choose 2 +
            (Native.parameters N).ell.choose 2) := by
  rw [completedAlgorithmSourceMacroCount, completedAlgorithm_query_count,
    ShortDLP.DeclaredStage.declaredStage_sourceMacroCount]
  simp [ShortDLP.firstBits]

/-- The same actual completed members retain the two inverse-QFT reversal
constructions on each of their original-width paths. -/
public lemma completedAlgorithm_swap_count {N : Nat}
    (input : Canonical.Input N) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count "swap" path =
      16 * count *
        (((Native.parameters N).ell + (Native.parameters N).m) / 2 +
          (Native.parameters N).ell / 2) := by
  rw [completedAlgorithmSourceMacroCount, completedAlgorithm_query_count,
    ShortDLP.DeclaredStage.declaredStage_sourceMacroCount]
  simp [ShortDLP.firstBits]

private lemma completedWidths_sameBit {n : Nat} (pair : RSA.RSAKeyPairBits n)
    (positive : 1 ≤ n) :
    (Native.parameters pair.modulus).ell + (Native.parameters pair.modulus).m =
        n + 1 + (n + 2) / 2 ∧
      (Native.parameters pair.modulus).ell = (n + 2) / 2 := by
  constructor
  · simp only [Native.parameters, shortLogBits_sameBit pair positive,
      tradeoffBits_sameBit pair positive, RSA.GeneratorOrder.m,
      RSA.GeneratorOrder.ell]
    omega
  · simp only [Native.parameters, tradeoffBits_sameBit pair positive,
      RSA.GeneratorOrder.ell]

/-- The completed candidate retains the original same-bit Hadamard source
formula on every actual path, including all sixteen observations per batch. -/
public lemma completedAlgorithm_hadamard_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count "hadamard" path =
      32 * count * (n + 1 + 2 * ((n + 2) / 2)) := by
  rw [completedAlgorithm_hadamard_count]
  obtain ⟨first, ell⟩ := completedWidths_sameBit pair positive
  rw [ell] at first
  rw [ell, first]
  ring

/-- Both completed inverse-QFT constructions retain the original same-bit
controlled-phase source statistic. -/
public lemma completedAlgorithm_controlledPhase_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count
      "controlled-phase" path =
        8 * count *
          ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
            ((n + 2) / 2) * ((n + 2) / 2 - 1)) := by
  rw [completedAlgorithm_controlledPhase_count]
  obtain ⟨first, ell⟩ := completedWidths_sameBit pair positive
  rw [first, ell]
  exact QuantumAlg.ChooseTwo.weighted_choose_two_sum count _ _

/-- The completed candidate's actual same-bit SWAP source count equals the
preserved sixteen-member formula at every requested batch count. -/
public lemma completedAlgorithm_swap_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    completedAlgorithmSourceMacroCount base noQuantum input count "swap" path =
      16 * count *
        ((n + 1 + (n + 2) / 2) / 2 + ((n + 2) / 2) / 2) := by
  rw [completedAlgorithm_swap_count]
  obtain ⟨first, ell⟩ := completedWidths_sameBit pair positive
  rw [first, ell]

/-- An independent literal-classical allowance for the actual completed
schedule. Every later batch includes its own selected-result pack and reset. -/
public def completedClassicalOperationBudget (N : Nat) :
    Nat → Nat
  | 0 => 0
  | laterCount + 1 =>
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (Finite.Cleanup.completedEventBudget N laterCount)

/-- Each path of the completed candidate respects its own classical-event
allowance, including the classical zero-count branch. -/
public lemma completedAlgorithm_classicalOperation_le_budget {N : Nat}
    (input : Canonical.Input N) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Finite.completedAlgorithm base noQuantum input count).run.code.resourcePool path) ≤
        completedClassicalOperationBudget N count := by
  cases count with
  | zero =>
      change ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (0 : ResourcePool (Native.Declared.model N)) ≤ 0
      exact le_of_eq
        (ResourcePool.weightedCount_zero Resource.Event.classicalOperationWeight)
  | succ laterCount =>
      exact ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
        (Finite.Cleanup.completed_resourcePool_le
          base noQuantum N input laterCount path)

/-- Every actual same-bit completed path pays at most one linear allowance
per requested batch; zero batches emit no classical-operation event. -/
public lemma completedAlgorithm_classicalOperation_sameBit_le_linear {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Finite.completedAlgorithm base noQuantum input count).run.code.resourcePool path) ≤
        count * (2 ^ 52 * n + 1) := by
  cases count with
  | zero =>
      rw [Nat.zero_mul, Finite.completedAlgorithm_zero_resourcePool]
      exact le_of_eq
        (ResourcePool.weightedCount_zero Resource.Event.classicalOperationWeight)
  | succ laterCount =>
      exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
        (Finite.Cleanup.completed_resourcePool_le
          base noQuantum pair.modulus input laterCount path)).trans
            (Finite.Cleanup.completedEventBudget_classicalWeight_le_linear
              pair positive laterCount)

/-- Every actual same-bit completed run obeys the complete original cubic
classical-operation ceiling, with each further result pack explicitly paid. -/
public lemma completedAlgorithm_classicalOperation_sameBit_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (count : Nat)
    (path : (Finite.completedAlgorithm base noQuantum input count).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Finite.completedAlgorithm base noQuantum input count).run.code.resourcePool path) ≤
        2 ^ 54 * count * n ^ 3 + 2 := by
  cases count with
  | zero =>
      have bounded := completedAlgorithm_classicalOperation_le_budget
        base noQuantum input 0 path
      simp only [completedClassicalOperationBudget] at bounded
      omega
  | succ laterCount =>
      exact (completedAlgorithm_classicalOperation_le_budget
        base noQuantum input (laterCount + 1) path).trans
          (Finite.Cleanup.completedEventBudget_classicalWeight_le_cubic
            pair positive laterCount)

/-- Source-construction counts of the ordinary named public algorithm. -/
public def algorithmSourceMacroCount {N : Nat} (input : Canonical.Input N)
    (η : Real) (name : String)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) : Nat :=
  completedAlgorithmSourceMacroCount base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η) name path

/-- The named public algorithm makes exactly sixteen group queries per
calibrated completed batch, including every paid intermediate cleanup. -/
public lemma algorithm_query_count {N : Nat} (input : Canonical.Input N)
    (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.oracleWeight
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) =
        16 * NativeFiniteRetry.Calibration.retryCount η :=
  completedAlgorithm_query_count base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η) path

/-- The named completed run has no peripheral Toffoli event on any actual
path. Its declared group-operation oracle is a separate query coordinate. -/
public lemma algorithm_toffoli_count {N : Nat} (input : Canonical.Input N)
    (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.count (model := Native.Declared.model N)
      (.gate AlgorithmGate.Coordinate.toffoli)
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) = 0 :=
  Finite.completedAlgorithm_toffoli_count base noQuantum input
    (NativeFiniteRetry.Calibration.retryCount η) path

/-- The named completed run's actual CNOT count is bounded by the expanded
controlled-phase and SWAP constructions in its sixteen members per batch. -/
public lemma algorithm_cnot_count_le {N : Nat} (input : Canonical.Input N)
    (η : Real)
    (etaPositive : 0 < η) (etaLessOne : η < 1)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.count (model := Native.Declared.model N)
      (.gate AlgorithmGate.Coordinate.cnot)
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) ≤
      2 * algorithmSourceMacroCount base noQuantum input η
        "controlled-phase" path +
      3 * algorithmSourceMacroCount base noQuantum input η "swap" path := by
  have bounded := Finite.completedAlgorithm_gate_count_le_positive
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η)
      (NativeFiniteRetry.Calibration.realRetryCount_pos η etaPositive etaLessOne) .cnot path
  have macros :
      2 * algorithmSourceMacroCount base noQuantum input η
          "controlled-phase" path +
        3 * algorithmSourceMacroCount base noQuantum input η "swap" path =
      16 * NativeFiniteRetry.Calibration.retryCount η *
        (2 * ShortDLP.DeclaredStage.sourceMacroCount
          N (Native.parameters N) "controlled-phase" +
         3 * ShortDLP.DeclaredStage.sourceMacroCount
           N (Native.parameters N) "swap") := by
    simp only [algorithmSourceMacroCount, completedAlgorithmSourceMacroCount,
      algorithm_query_count]
    ring
  rw [macros]
  simpa only [Canonical.OracleModel.Native.Declared.member_cnot_count,
    reduceCtorEq, if_false, Nat.mul_zero, Nat.add_zero] using bounded

/-- The named completed run's actual one-qubit gates include the expanded
member constructions and every reserved physical-reset correction. -/
public lemma algorithm_singleQubit_count_le {N : Nat} (input : Canonical.Input N)
    (η : Real)
    (etaPositive : 0 < η) (etaLessOne : η < 1)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.count (model := Native.Declared.model N)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) ≤
      algorithmSourceMacroCount base noQuantum input η "hadamard" path +
        3 * algorithmSourceMacroCount base noQuantum input η
          "controlled-phase" path +
        (16 + 17 * Nat.pred (NativeFiniteRetry.Calibration.retryCount η)) *
          ((Native.parameters N).ell + (Native.parameters N).m +
            (Native.parameters N).ell + (Native.parameters N).workspaceBits) := by
  have bounded := Finite.completedAlgorithm_gate_count_le_positive
    base noQuantum input (NativeFiniteRetry.Calibration.retryCount η)
      (NativeFiniteRetry.Calibration.realRetryCount_pos η etaPositive etaLessOne)
      .singleQubit path
  have macros :
      algorithmSourceMacroCount base noQuantum input η "hadamard" path +
        3 * algorithmSourceMacroCount base noQuantum input η
          "controlled-phase" path =
      16 * NativeFiniteRetry.Calibration.retryCount η *
        (ShortDLP.DeclaredStage.sourceMacroCount N (Native.parameters N) "hadamard" +
         3 * ShortDLP.DeclaredStage.sourceMacroCount
           N (Native.parameters N) "controlled-phase") := by
    simp only [algorithmSourceMacroCount, completedAlgorithmSourceMacroCount,
      algorithm_query_count]
    ring
  rw [macros]
  simpa only [Canonical.OracleModel.Native.Declared.member_singleQubit_count,
    ↓reduceIte, Nat.mul_one, ShortDLP.totalQubits, ShortDLP.firstBits] using bounded

/-- The named public algorithm's actual Hadamard source-construction count. -/
public lemma algorithm_hadamard_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    algorithmSourceMacroCount base noQuantum input η "hadamard" path =
      32 * NativeFiniteRetry.Calibration.retryCount η *
        (n + 1 + 2 * ((n + 2) / 2)) :=
  completedAlgorithm_hadamard_count_sameBit base noQuantum pair positive input
    (NativeFiniteRetry.Calibration.retryCount η) path

/-- Both actual inverse QFTs retain the same-bit controlled-phase statistic
on the named public completed algorithm. -/
public lemma algorithm_controlledPhase_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    algorithmSourceMacroCount base noQuantum input η "controlled-phase" path =
      8 * NativeFiniteRetry.Calibration.retryCount η *
        ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
          ((n + 2) / 2) * ((n + 2) / 2 - 1)) :=
  completedAlgorithm_controlledPhase_count_sameBit
    base noQuantum pair positive input (NativeFiniteRetry.Calibration.retryCount η) path

/-- Both inverse-QFT reversals retain the same-bit SWAP statistic on the
named public completed algorithm. -/
public lemma algorithm_swap_count_sameBit {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    algorithmSourceMacroCount base noQuantum input η "swap" path =
      16 * NativeFiniteRetry.Calibration.retryCount η *
        ((n + 1 + (n + 2) / 2) / 2 + ((n + 2) / 2) / 2) :=
  completedAlgorithm_swap_count_sameBit
    base noQuantum pair positive input (NativeFiniteRetry.Calibration.retryCount η) path

/-- The actual CNOT coordinate has a closed same-bit bound on the named
completed run; both inverse QFTs and their SWAP reversals are included. -/
public lemma algorithm_cnot_count_sameBit_le {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (etaPositive : 0 < η) (etaLessOne : η < 1)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.count (model := Native.Declared.model pair.modulus)
      (.gate AlgorithmGate.Coordinate.cnot)
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) ≤
      2 * (8 * NativeFiniteRetry.Calibration.retryCount η *
        ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
          ((n + 2) / 2) * ((n + 2) / 2 - 1))) +
      3 * (16 * NativeFiniteRetry.Calibration.retryCount η *
        ((n + 1 + (n + 2) / 2) / 2 + ((n + 2) / 2) / 2)) := by
  simpa only [algorithm_controlledPhase_count_sameBit base noQuantum pair
      positive input η path,
    algorithm_swap_count_sameBit base noQuantum pair positive input η path] using
    algorithm_cnot_count_le base noQuantum input η etaPositive etaLessOne path

/-- The actual one-qubit coordinate has a closed same-bit bound, charging
the corrections of all completed physical resets. -/
public lemma algorithm_singleQubit_count_sameBit_le {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (etaPositive : 0 < η) (etaLessOne : η < 1)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.count (model := Native.Declared.model pair.modulus)
      (.gate AlgorithmGate.Coordinate.singleQubit)
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) ≤
      32 * NativeFiniteRetry.Calibration.retryCount η *
        (n + 1 + 2 * ((n + 2) / 2)) +
      3 * (8 * NativeFiniteRetry.Calibration.retryCount η *
        ((n + 1 + (n + 2) / 2) * (n + 1 + (n + 2) / 2 - 1) +
          ((n + 2) / 2) * ((n + 2) / 2 - 1))) +
      (16 + 17 * Nat.pred (NativeFiniteRetry.Calibration.retryCount η)) *
        (3 * n + 2 * ((n + 2) / 2) + 1) := by
  have width :
      (Native.parameters pair.modulus).ell + (Native.parameters pair.modulus).m +
        (Native.parameters pair.modulus).ell +
          (Native.parameters pair.modulus).workspaceBits =
        3 * n + 2 * ((n + 2) / 2) + 1 := by
    simpa only [ShortDLP.totalQubits, ShortDLP.firstBits] using
      Native.nativeOracle_qubitCount_sameBit pair positive
  simpa only [algorithm_hadamard_count_sameBit base noQuantum pair
      positive input η path,
    algorithm_controlledPhase_count_sameBit base noQuantum pair
      positive input η path, width] using
    algorithm_singleQubit_count_le base noQuantum input η etaPositive etaLessOne path

/-- The named public completed algorithm pays every classical operation,
including the extra result packs, within the original same-bit cubic reserve. -/
public lemma algorithm_classicalOperation_sameBit_le_cubic {n : Nat}
    (pair : RSA.RSAKeyPairBits n) (positive : 1 ≤ n)
    (input : Canonical.Input pair.modulus) (η : Real)
    (path : (Finite.completedAlgorithm base noQuantum input
      (NativeFiniteRetry.Calibration.retryCount η)).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((Finite.completedAlgorithm base noQuantum input
        (NativeFiniteRetry.Calibration.retryCount η)).run.code.resourcePool path) ≤
        2 ^ 54 * NativeFiniteRetry.Calibration.retryCount η * n ^ 3 + 2 :=
  completedAlgorithm_classicalOperation_sameBit_le_cubic
    base noQuantum pair positive input (NativeFiniteRetry.Calibration.retryCount η) path

end

end QuantumAlg.Factoring.EkeraHastadStyle
