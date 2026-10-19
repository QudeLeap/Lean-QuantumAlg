/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Real
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Real
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Real.Execution

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.First.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Round.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Completion
import all QuantumAlg.Core.Execution.Classical.Predicate
import all QuantumAlg.Core.Execution.Restart
import all QuantumAlg.Core.Execution.Input.Successor
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Reassociation
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Depth
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Real.Scalar
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.ClassicalSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Peripheral
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Amplification.Model

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Events
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.Event
import QuantumAlg.Util.Nat.ChooseTwo

/-!
# Full declared ECDLP recovery at arbitrary positive real failure targets

The public order determines its own certified preparation expansion. One
complete named execution supplies success, all output/reference fibers,
borrowed restoration, complete-run quantum time and the original scalar resources.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget

noncomputable section
open Canonical.QueryModel Canonical.QueryModel.Recovery
variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The actual public problem has exactly the requested real success threshold. -/
public lemma ecdlpReal_successLB (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η)
    (environment : (Sampling.executionModel I).Environment)
    (witness : (problem I η positive).Witness) :
    ((problem I η positive).successLB environment witness).value = ENNReal.ofReal (1 - η) := by rfl

/-- The actual initialized run meets the full original input/output contract. -/
public lemma algorithm_solves (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η) :
    (algorithm I η).Solves (problem I η positive) :=
  complete_correct I η positive

/-- The hidden scalar is carried by the specification, outside the fixed program. -/
public def secretWitness (I : ECDLPInstance E) (η : Real) (positive : 0 < η)
    (secret : FiniteCyclicDLP.Canonical.Probability.SecretInput (Canonical.problem I)) :
    (problem I η positive).Witness := secret

/-- Every originally granted access retains exactly the original caller input domain. -/
public lemma source_admits_iff (I : ECDLPInstance E) (A : Canonical.Access I)
    (η : Real) (positive : 0 < η)
    (secret : FiniteCyclicDLP.Canonical.Probability.SecretInput (Canonical.problem I))
    {Reference : Register}
    (original : Execution.OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference) :
    (problem I η positive).Admits (Sampling.sourceEnvironment I A)
      (secretWitness I η positive secret) original ↔
        inputDomain I original.caller.localState := by
  constructor
  · intro admitted
    exact admitted.1.2
  · intro admitted
    exact ⟨⟨Sampling.sourceEnvironment_admissible I A, admitted⟩, trivial⟩

/-- The original access and caller domain satisfy the public validity predicate. -/
public lemma source_valid (I : ECDLPInstance E) (A : Canonical.Access I)
    (η : Real) (positive : 0 < η)
    (secret : FiniteCyclicDLP.Canonical.Probability.SecretInput (Canonical.problem I))
    {Reference : Register}
    (original : Execution.OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference)
    (domain : inputDomain I original.caller.localState) :
    (problem I η positive).valid (Sampling.sourceEnvironment I A)
      (secretWitness I η positive secret) original.caller.localState :=
  ((source_admits_iff I A η positive secret original).mpr domain).1

/-- Source callers satisfy initialization before the fixed public program runs. -/
public lemma source_initialized (I : ECDLPInstance E) (A : Canonical.Access I)
    (η : Real) (positive : 0 < η)
    (secret : FiniteCyclicDLP.Canonical.Probability.SecretInput (Canonical.problem I))
    {Reference : Register}
    (original : Execution.OracleInput (Sampling.executionModel I).classicalOracles
      (Sampling.pre I) Reference) :
    (problem I η positive).initialization (Sampling.sourceEnvironment I A)
      (secretWitness I η positive secret) original.localState := by
  trivial

/-- The exact local repeat count selected by the actual public algorithm. -/
public abbrev repetitionCount (I : ECDLPInstance E) (η : Real) : Nat := realRepetitionCount I η

/-- The field and sample widths are exactly the reviewed real logarithmic ceilings. -/
public lemma ecdlpReal_widths (I : ECDLPInstance E) :
    fieldWidth E = ⌈Real.logb 2 p⌉₊ ∧
      scalarWidth I = ⌈Real.logb 2 (12 * I.subgroupOrder : Nat)⌉₊ := by
  have field : ⌈Real.logb 2 p⌉₊ = Nat.clog 2 p := Real.natCeil_logb_natCast 2 p
  have scalar : ⌈Real.logb 2 (12 * I.subgroupOrder : Nat)⌉₊ =
      Nat.clog 2 (12 * I.subgroupOrder) := Real.natCeil_logb_natCast 2 _
  rw [field, scalar]
  exact ⟨rfl, rfl⟩

/-- The original scalar allowance has the reviewed explicit logarithmic qubit count. -/
public lemma ecdlpReal_qubits_closed (I : ECDLPInstance E) :
    Scalar.qubits (fieldWidth E) (scalarWidth I) =
      2 * ⌈Real.logb 2 (12 * I.subgroupOrder : Nat)⌉₊ + 2 * ⌈Real.logb 2 p⌉₊ + 1 := by
  rw [(ecdlpReal_widths I).1, (ecdlpReal_widths I).2]
  unfold Scalar.qubits
  omega

/-- Prime order gives the reviewed selected-family floor inside the direct logarithmic count. -/
public lemma ecdlpReal_repetitionCount_eq (I : ECDLPInstance E) (η : Real) :
    repetitionCount I η =
      ⌈Real.log η / Real.log (1 - (I.subgroupOrder : Real) * (I.subgroupOrder - 1) /
        2 ^ (2 * scalarWidth I + 2))⌉₊ := by
  have floor := FiniteCyclicDLP.Concrete.Amplification.attemptFloor_eq_primeOrder
    (Canonical.problem I) I.subgroupOrder_prime
  have positive := I.subgroupOrder_prime.two_le
  have denominator :
      (FiniteCyclicDLP.Concrete.Amplification.successDenominator (Canonical.problem I) : Real) =
        2 ^ (2 * scalarWidth I + 2) := by
    change ((4 * (2 ^ scalarWidth I) ^ 2 : Nat) : Real) = _
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, Nat.mul_comm (scalarWidth I) 2, pow_add]
    norm_num [mul_comm]
  have same : Sampling.Reuse.successFloor I =
      (I.subgroupOrder : Real) * (I.subgroupOrder - 1) / 2 ^ (2 * scalarWidth I + 2) := by
    change FiniteCyclicDLP.Concrete.Amplification.attemptFloor (Canonical.problem I) = _
    rw [floor, denominator]
    congr 1
    change ((I.subgroupOrder * (I.subgroupOrder - 1) : Nat) : Real) = _
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ I.subgroupOrder), Nat.cast_one]
  simp only [repetitionCount, realRepetitionCount, same]

/-- Seven resource coordinates refer to one actual complete public execution path. -/
@[expose] public def SevenCoordinateBounds (I : ECDLPInstance E)
    (η : Real)
    (path : (algorithm I η).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    (algorithm I η).run.code.peakResidentSpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits (fieldWidth E) (scalarWidth I) else 0) ∧
  ResourcePool.count (model := Sampling.executionModel I) (.gate .toffoli)
    ((algorithm I η).run.code.resourcePool path) = 0 ∧
  ResourcePool.count (model := Sampling.executionModel I) (.gate .cnot)
    ((algorithm I η).run.code.resourcePool path) ≤
      repetitionCount I η * (2 * (scalarWidth I) ^ 2 + 4 * scalarWidth I +
        6 * (scalarWidth I / 2)) ∧
  ResourcePool.count (model := Sampling.executionModel I) (.gate .singleQubit)
    ((algorithm I η).run.code.resourcePool path) ≤
      repetitionCount I η * (3 * (scalarWidth I) ^ 2 + 25 * scalarWidth I + 4 * fieldWidth E + 3) ∧
  (algorithm I η).quantumTime path ≤
    Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I) (repetitionCount I η) ∧
  (algorithm I η).run.code.peakResidentSpace path .classicalBits ≤
    max (18 * (scalarWidth I) ^ 2 + 70 * scalarWidth I + 70)
      (18 * (fieldWidth E) ^ 2 + 72 * fieldWidth E + 69) +
        6 * fieldWidth E + 4 * scalarWidth I + 8 ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm I η).run.code.resourcePool path) ≤
      repetitionCount I η * (248 * fieldWidth E * scalarWidth I + 686 * scalarWidth I + 119) + 1

/-- Closed scalar resources follow from the same actual code and
independent complete-run allowances. -/
public lemma algorithm_sevenCoordinates (I : ECDLPInstance E)
    (η : Real) (path : (algorithm I η).run.code.Path) :
    SevenCoordinateBounds I η path := by
  let expansion := sourceExpansion I
  let nontrivial := I.subgroupOrder_prime.two_le
  have pool := ecdlpRecovery_code_events_le I expansion nontrivial (repetitionCount I η) path
  have resident := ecdlpRecovery_code_resident_le I expansion nontrivial
    (repetitionCount I η) path
  unfold SevenCoordinateBounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    have quantum := (whole_memory_quantum_coordinates I dimension).1
    rw [original_qubits_scalar] at quantum
    exact (resident (.quantumSystems dimension)).trans_eq quantum
  · apply Nat.eq_zero_of_le_zero
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .toffoli)).trans
      ((whole_budget_gate_scalar I expansion nontrivial
        (repetitionCount I η) .toffoli).trans_eq (Nat.mul_zero _))
  · have ceiling :=
      whole_budget_gate_scalar I expansion nontrivial (repetitionCount I η) .cnot
    rw [real_cnot_closed] at ceiling
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .cnot)).trans ceiling
  · have ceiling :=
      whole_budget_gate_scalar I expansion nontrivial (repetitionCount I η) .singleQubit
    rw [real_single_closed] at ceiling
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .singleQubit)).trans ceiling
  · apply (Circuit.quantumTime_le_unitDepth _ _).trans
    have depth := Circuit.depth_le_weightedCount_of_pool_le
      (code I expansion nontrivial (repetitionCount I η)) (fun _ => 1)
      (eventBudget I expansion nontrivial (repetitionCount I η)) path pool
    have ceiling : ResourcePool.weightedCount (fun _ => 1)
        (eventBudget I expansion nontrivial (repetitionCount I η)) ≤
        Scalar.wholeRunEvents (fieldWidth E) (scalarWidth I) (repetitionCount I η) := by
      simpa [ResourcePool.weightedCount, Multiset.map_const'] using
        whole_budget_events_scalar I expansion nontrivial (repetitionCount I η)
    exact depth.trans ceiling
  · exact ((resident .classicalBits).trans (whole_memory_classical_scalar I).1).trans_eq
      (real_resident_closed _ _)
  · have ceiling := whole_budget_classical_scalar I expansion nontrivial (repetitionCount I η)
    rw [real_classical_closed] at ceiling
    exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool).trans
      ceiling

/-- Exactly the chosen number of original ordinary group-action queries is an upper bound. -/
public lemma algorithm_queryCount (I : ECDLPInstance E)
    (η : Real) (path : (algorithm I η).run.code.Path) :
    ResourcePool.count (model := Sampling.executionModel I) (.oracle Coordinate.groupAction)
      ((algorithm I η).run.code.resourcePool path) ≤ repetitionCount I η :=
  ((ResourcePool.le_iff_count.mp (ecdlpRecovery_code_events_le I (sourceExpansion I)
    I.subgroupOrder_prime.two_le (repetitionCount I η) path)) _).trans
      (whole_budget_query_scalar I (sourceExpansion I) I.subgroupOrder_prime.two_le _)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget

noncomputable section

/-! Closed complete-run time ceilings for the independent problem.
The unit-event allowance conservatively bounds canonical quantum time. -/

private lemma quantumWeight_le_card {model : ExecutionModel}
    (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.quantumDuration pool ≤ pool.card := by
  induction pool using Multiset.induction_on with
  | empty => simp [ResourcePool.weightedCount]
  | cons event rest ih =>
      simp only [ResourcePool.weightedCount, Multiset.map_cons, Multiset.sum_cons,
        Multiset.card_cons] at *
      exact (Nat.add_le_add (Resource.Event.quantumDuration_le_one event) ih).trans_eq
        (Nat.add_comm 1 rest.card)

private lemma twice_choose_add (width : Nat) :
    2 * width.choose 2 + width = width ^ 2 := by
  rw [ChooseTwo.twice_choose_two]
  cases width with
  | zero => rfl
  | succ width => simp only [Nat.add_sub_cancel]; ring

open EllipticCurve EllipticCurve.PrimeFieldShortWeierstrass
open ECDLP.Canonical.QueryModel ECDLP.Canonical.QueryModel.Recovery

/-- A closed independent ceiling for complete-run quantum time. -/
@[expose] public def ecdlpRealQuantumTimeCeiling (f t count : Nat) : Nat :=
  2 * t + 2 * f + 2 + count * (5 * t ^ 2 + 248 * f * t + 721 * t +
    8 * f + 6 * (t / 2) + 125)

private lemma ecdlpReal_roundEvents_eq_polynomial (f t : Nat) :
    Scalar.roundEvents f t =
      5 * t ^ 2 + 248 * f * t + 721 * t + 8 * f + 6 * (t / 2) + 125 := by
  have pairs := twice_choose_add t
  unfold Scalar.roundEvents Scalar.roundSingleQubit Scalar.roundCnot
    Scalar.roundMeasurements Scalar.recoveryEvents Scalar.qubits
  nlinarith

private lemma ecdlpReal_wholeRunEvents_eq_polynomial (f t count : Nat) :
    Scalar.wholeRunEvents f t count = ecdlpRealQuantumTimeCeiling f t count := by
  unfold Scalar.wholeRunEvents Scalar.qubits ecdlpRealQuantumTimeCeiling
  rw [ecdlpReal_roundEvents_eq_polynomial]
  ring

/-- The bound is on the independent complete event specification, including count zero. -/
private lemma ecdlpReal_wholeProblem_quantumTimeLimit_le
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (ECDLP.Canonical.problem I).order) (count : Nat) :
    (wholeProblem I expansion nontrivial count).quantumTimeLimit ≤
      ecdlpRealQuantumTimeCeiling (fieldWidth E) (scalarWidth I) count := by
  change ResourcePool.weightedCount Resource.Event.quantumDuration
    (eventBudget I expansion nontrivial count) ≤ _
  exact (quantumWeight_le_card _).trans
    ((whole_budget_events_scalar I expansion nontrivial count).trans_eq
      (ecdlpReal_wholeRunEvents_eq_polynomial _ _ _))

public lemma ecdlpReal_problem_quantumTimeLimit_le {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E)
    (η : Real) (positive : 0 < η) :
    (ECDLP.RealTarget.problem I η positive).quantumTimeLimit ≤
      ecdlpRealQuantumTimeCeiling (fieldWidth E) (scalarWidth I)
        (ECDLP.RealTarget.repetitionCount I η) := by
  exact ecdlpReal_wholeProblem_quantumTimeLimit_le I (ECDLP.RealTarget.sourceExpansion I)
    I.subgroupOrder_prime.two_le _

/-- The zero-round ceiling retains the original prefix allowance. -/
public lemma ecdlpRealQuantumTimeCeiling_zero_count (f t : Nat) :
    ecdlpRealQuantumTimeCeiling f t 0 = 2 * t + 2 * f + 2 := by
  simp [ecdlpRealQuantumTimeCeiling]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.RealTarget
