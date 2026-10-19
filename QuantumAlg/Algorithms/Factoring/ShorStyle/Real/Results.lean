/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Real
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Real
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Real.Execution

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Protocol
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Real.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Quantum
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Events
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Context

import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.Event

/-!
# Complete Shor factoring for arbitrary real failure targets

One actual machine supplies original factoring success, every full joint
output/reference fiber, borrowed restoration and all event, space and depth
obligations. Initialization and every reused round belong to the same code.
Unknown distinct primes are theorem-side data, never executable inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle.RealTarget

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- The same real-target problem accepts every legal unknown-factor specification witness. -/
public def factorWitness (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) :
    (problem N input η positive).Witness := witness

/-- Source access admits every legal factor witness and normalized external-reference extension. -/
public lemma source_admits (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (ShorStyle.executionModel N).classicalOracles pre Reference) :
    (problem N input η positive).Admits (sourceEnvironment N input)
      (factorWitness N input η positive witness) original :=
  ⟨rfl, trivial⟩

/-- The source interpretation satisfies the public local input domain. -/
public lemma source_valid (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (ShorStyle.executionModel N).classicalOracles pre Reference) :
    (problem N input η positive).valid (sourceEnvironment N input)
      (factorWitness N input η positive witness) original.caller.localState := by
  rfl

/-- Every original normalized caller satisfies the source initialization contract. -/
public lemma source_initialized (N : Nat) (input : Canonical.Input N)
    (η : Real) (positive : 0 < η)
    (witness : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : Execution.OracleInput (ShorStyle.executionModel N).classicalOracles pre Reference) :
    (problem N input η positive).initialization (sourceEnvironment N input)
      (factorWitness N input η positive witness) original.localState := by
  trivial

/-- The same complete protocol carries exactly the requested real success threshold. -/
public lemma shorReal_problem_successLB (N : Nat)
    (input : Canonical.Input N) (η : Real) (positive : 0 < η)
    (actual : (ShorStyle.executionModel N).Environment)
    (witness : (problem N input η positive).Witness) :
    ((problem N input η positive).successLB actual witness).value = ENNReal.ofReal (1 - η) := by
  rfl

/-- The ordinary named algorithm meets all seven obligations from every original caller. -/
public lemma algorithm_solves (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (positive : 0 < η) :
    (algorithm N input η).Solves (problem N input η positive) :=
  complete_correct N input η positive

/-- The original modulus and real target select the exact direct logarithmic retry count. -/
public def repetitionCount (N : Nat) (η : Real) : Nat :=
  Machine.RealTarget.repetitionCount N η

/-- The public count is exactly the reviewed real logarithmic ceiling at the minimal width. -/
public lemma shorReal_repetitionCount_eq (N : Nat) (η : Real) :
    repetitionCount N η =
      ⌈Real.log η / Real.log (1 - 1 / (48 * (⌈Real.logb 2 N⌉₊ : Real)))⌉₊ := by
  have width : ⌈Real.logb 2 N⌉₊ = Nat.clog 2 N := Real.natCeil_logb_natCast 2 N
  rw [width]
  rfl

/-- A unit failure target selects zero actual attempts. -/
public lemma shorReal_repetitionCount_one (N : Nat) : repetitionCount N 1 = 0 :=
  Machine.RealTarget.shorRealTarget_repetitionCount_one N

/-- A unit target still pays the actual latch initialization and terminal result pack. -/
public lemma shorReal_zero_classicalOperations (N : Nat)
    (input : Canonical.Input N)
    (path : (algorithm N input 1).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm N input 1).run.code.resourcePool path) = 2 := by
  have atZero (count : Nat) (zero : count = 0)
      (originalPath : (Machine.code pre pre_quantumWires N
        input count).Path) :
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((Machine.code pre pre_quantumWires N
          input count).resourcePool originalPath) =
        2 := by
    subst count
    exact Machine.zero_classical_operations pre pre_quantumWires N _ originalPath
  exact atZero _ (Machine.RealTarget.shorRealTarget_repetitionCount_one N) path

private lemma original_resident_zero : pre.residentSpace = 0 := by
  funext axis
  cases axis <;> rfl

private lemma original_auxiliary_zero : pre.auxiliarySpace = 0 := by
  funext axis
  cases axis <;> rfl

/-- Seven independent scalar observations on the same original factoring execution path. -/
@[expose] public def SevenCoordinateBounds (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((algorithm N input η).run.code.peakResidentSpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0) ∧
    ((algorithm N input η).run.code.peakAuxiliarySpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0)) ∧
  ResourcePool.count (model := executionModel N) (.gate .toffoli)
    ((algorithm N input η).run.code.resourcePool path) ≤ 0 ∧
  ResourcePool.count (model := executionModel N) (.gate .cnot)
    ((algorithm N input η).run.code.resourcePool path) ≤
      repetitionCount N η * (4 * (Nat.clog 2 N) ^ 2 + Nat.clog 2 N) ∧
  ResourcePool.count (model := executionModel N) (.gate .singleQubit)
    ((algorithm N input η).run.code.resourcePool path) ≤
      repetitionCount N η * (6 * (Nat.clog 2 N) ^ 2 + 4 * Nat.clog 2 N) ∧
  (algorithm N input η).quantumTime path ≤
    Scalar.wholeRunDepth N (repetitionCount N η) ∧
  (((algorithm N input η).run.code.peakResidentSpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N η)) ∧
    ((algorithm N input η).run.code.peakAuxiliarySpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N η))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm N input η).run.code.resourcePool path) ≤
      repetitionCount N η *
        (56 * (Nat.clog 2 N) ^ 2 + 222 * Nat.clog 2 N + 316) + 2

/-- The complete same-run scalar theorem is established for arbitrary modulus and retry target. -/
public lemma algorithm_sevenCoordinates (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path) :
    SevenCoordinateBounds N input η path := by
  let count := Machine.RealTarget.repetitionCount N η
  have pool := Machine.code_pool_le pre pre_quantumWires N input count path
  have resident := Machine.code_resident_le pre pre_quantumWires N input count path
  have auxiliary := Machine.code_auxiliary_le pre pre_quantumWires N input count path
  rw [original_resident_zero, zero_add] at resident
  rw [original_auxiliary_zero, zero_add] at auxiliary
  unfold SevenCoordinateBounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    have quantum := Scalar.machine_quantum_coordinate N count dimension
    exact ⟨(resident (.quantumSystems dimension)).trans_eq quantum,
      (auxiliary (.quantumSystems dimension)).trans_eq quantum⟩
  · have ceiling := Scalar.machine_gate_count N count .toffoli
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .toffoli)).trans_eq
      (ceiling.trans (Nat.mul_zero _))
  · have ceiling := Scalar.machine_gate_count N count .cnot
    rw [Scalar.roundCnot_closed] at ceiling
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .cnot)).trans_eq ceiling
  · have ceiling := Scalar.machine_gate_count N count .singleQubit
    rw [Scalar.roundSingleQubit_closed] at ceiling
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .singleQubit)).trans_eq ceiling
  · exact (Circuit.quantumTime_le_unitDepth _ _).trans
      ((Machine.code_depth_le pre pre_quantumWires N input count (fun _ => 1) path).trans
        (Scalar.machine_depth_scalar N count))
  · have memory := Scalar.machine_classical_coordinate N count
    exact ⟨(resident .classicalBits).trans_eq memory,
      (auxiliary .classicalBits).trans_eq memory⟩
  · have observed :
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          ((algorithm N input η).run.code.resourcePool path) ≤
        ResourcePool.weightedCount Resource.Event.classicalOperationWeight
          (Machine.eventEnvelope N count) :=
      ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool
    have ledger := Scalar.machine_classical_operations_le N count
    have polynomial := Scalar.classicalOperations_closed_le N count
    exact observed.trans (ledger.trans polynomial)

/-- The unit-event chronological bound also counts all classical work and measurements. -/
public lemma algorithm_wholeRunDepth (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path) :
    (algorithm N input η).run.code.depth (fun _ => 1) path ≤
      Scalar.wholeRunDepth N (repetitionCount N η) :=
  (Machine.code_depth_le pre pre_quantumWires N
    input (Machine.RealTarget.repetitionCount N η)
    (fun _ => 1) path).trans (Scalar.machine_depth_scalar _ _)

/-- Every declared query coordinate is observed on the same original named computation. -/
public lemma algorithm_queryCount (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path)
    (coordinate : (ShorStyle.executionModel N).OracleCoordinate) :
    ResourcePool.count (model := executionModel N) (.oracle coordinate)
      ((algorithm N input η).run.code.resourcePool path) ≤ repetitionCount N η := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Machine.RealTarget.repetitionCount N η) path
  exact ((ResourcePool.le_iff_count.mp pool) (.oracle coordinate)).trans_eq
    (Scalar.machine_query_count N (Machine.RealTarget.repetitionCount N η) coordinate)

/-- Preparations retain their actual positive system dimension on the original execution. -/
public lemma algorithm_preparationCount (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.preparation dimension)
      ((algorithm N input η).run.code.resourcePool path) ≤
        if 2 = dimension then Scalar.qubits N else 0 := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Machine.RealTarget.repetitionCount N η) path
  exact ((ResourcePool.le_iff_count.mp pool) (.preparation dimension)).trans_eq
    (Scalar.machine_preparation_count N (Machine.RealTarget.repetitionCount N η) dimension)

/-- Phase and physical-reset measurements use the same full computation and dimension. -/
public lemma algorithm_measurementCount (N : Nat)
    (input : Canonical.Input N) (η : Real)
    (path : (algorithm N input η).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.measurement dimension)
      ((algorithm N input η).run.code.resourcePool path) ≤
        if 2 = dimension then repetitionCount N η * Scalar.roundMeasurements N else 0 := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Machine.RealTarget.repetitionCount N η) path
  exact ((ResourcePool.le_iff_count.mp pool) (.measurement dimension)).trans_eq
    (Scalar.machine_measurement_count N (Machine.RealTarget.repetitionCount N η) dimension)

end

end QuantumAlg.Factoring.ShorStyle.RealTarget

namespace QuantumAlg.Factoring.ShorStyle.RealTarget

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

private lemma quantumWeight_le_unit {model : ExecutionModel}
    (pool : ResourcePool model) :
    ResourcePool.weightedCount Resource.Event.quantumDuration pool ≤
      ResourcePool.weightedCount (fun _ => 1) pool := by
  simpa [ResourcePool.weightedCount, Multiset.map_const'] using quantumWeight_le_card pool

open Factoring.ShorStyle Factoring.ShorStyle.Canonical
open Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

/-- A closed independent ceiling for complete-run quantum time. -/
@[expose] public def shorRealQuantumTimeCeiling (n count : Nat) : Nat :=
  3 * n + count * (66 * n ^ 2 + 232 * n + 317) + 2

private lemma shorReal_roundEvents_le_polynomial (N : Nat) :
    Scalar.roundEvents N ≤ 66 * (modulusBits N) ^ 2 + 232 * modulusBits N + 317 := by
  have classical : Scalar.roundClassicalOperations N ≤
      56 * (modulusBits N) ^ 2 + 222 * modulusBits N + 316 := by
    rw [Scalar.roundClassicalOperations_polynomial]
    split_ifs <;> omega
  unfold Scalar.roundEvents
  rw [Scalar.roundSingleQubit_closed, Scalar.roundCnot_closed]
  unfold Scalar.roundMeasurements phaseBits Scalar.qubits
  omega

private lemma shorReal_wholeRunDepth_le_polynomial (N count : Nat) :
    Scalar.wholeRunDepth N count ≤ shorRealQuantumTimeCeiling (modulusBits N) count := by
  unfold Scalar.wholeRunDepth Scalar.qubits shorRealQuantumTimeCeiling
  exact Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left count (shorReal_roundEvents_le_polynomial N)) _) 2

/-- The bound is on the independent public Problem, for every real positive eta. -/
public lemma shorReal_problem_quantumTimeLimit_le (N : Nat)
    (input : Canonical.Input N)
    (η : Real) (positive : 0 < η) :
    (Factoring.ShorStyle.RealTarget.problem N input η positive).quantumTimeLimit ≤
      shorRealQuantumTimeCeiling (Nat.clog 2 N)
        (Factoring.ShorStyle.RealTarget.repetitionCount N η) := by
  change ResourcePool.weightedCount Resource.Event.quantumDuration
    (Machine.eventEnvelope N
      (Machine.RealTarget.repetitionCount N η)) ≤ _
  exact (quantumWeight_le_unit _).trans
    ((Scalar.machine_depth_scalar _ _).trans (shorReal_wholeRunDepth_le_polynomial N _))

/-- The zero-round ceiling retains the original prefix allowance. -/
public lemma shorRealQuantumTimeCeiling_zero_count (n : Nat) :
    shorRealQuantumTimeCeiling n 0 = 3 * n + 2 := by
  simp [shorRealQuantumTimeCeiling]

end

end QuantumAlg.Factoring.ShorStyle.RealTarget
