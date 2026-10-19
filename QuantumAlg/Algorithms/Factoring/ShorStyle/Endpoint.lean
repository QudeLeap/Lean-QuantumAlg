/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Specification
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Schedule
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Events
import all QuantumAlg.Core.Base.Depth.WeightedCost
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Complete original-input declared Shor factoring through the ordinary public entry

One actual machine supplies original factoring success, every full joint
output/reference fiber, borrowed restoration and all event, space and depth
obligations. Its real initialized and reused complete cycles use the same code.
Unknown distinct primes are theorem-side data, never executable inputs.
-/

namespace QuantumAlg.Factoring.ShorStyle

noncomputable section

open Canonical.DeclaredSource.Runtime

/-- The actual source-calibrated execution initializes, samples, recovers, resets and packs once. -/
public def algorithm (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) :
    Algorithm (executionModel N) pre (post N budget) (OutputShape N) :=
  Machine.algorithm pre pre_quantumWires N input budget

/-- The ordinary named algorithm meets all seven obligations from every original caller. -/
public lemma algorithm_solves (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    (algorithm N input budget).Solves (problem N input budget wellFormed) :=
  Machine.shorDeclared_machine_solves pre pre_quantumWires N input budget wellFormed

/-- The original modulus and rational target internally select the genuine retry count. -/
public def repetitionCount (N : Nat) (budget : FailureBudget) : Nat :=
  Canonical.retryCount N budget

private lemma original_resident_zero : pre.residentSpace = 0 := by
  funext axis
  cases axis <;> rfl

private lemma original_auxiliary_zero : pre.auxiliarySpace = 0 := by
  funext axis
  cases axis <;> rfl

/-- Seven independent scalar observations on the same original factoring execution path. -/
@[expose] public def SevenCoordinateBounds (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((algorithm N input budget).run.code.peakResidentSpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0) ∧
    ((algorithm N input budget).run.code.peakAuxiliarySpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0)) ∧
  ResourcePool.count (model := executionModel N) (.gate .toffoli)
    ((algorithm N input budget).run.code.resourcePool path) ≤ 0 ∧
  ResourcePool.count (model := executionModel N) (.gate .cnot)
    ((algorithm N input budget).run.code.resourcePool path) ≤
      repetitionCount N budget * Scalar.roundCnot N ∧
  ResourcePool.count (model := executionModel N) (.gate .singleQubit)
    ((algorithm N input budget).run.code.resourcePool path) ≤
      repetitionCount N budget * Scalar.roundSingleQubit N ∧
  (algorithm N input budget).quantumTime path ≤
    Scalar.wholeRunDepth N (repetitionCount N budget) ∧
  (((algorithm N input budget).run.code.peakResidentSpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N budget)) ∧
    ((algorithm N input budget).run.code.peakAuxiliarySpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N budget))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm N input budget).run.code.resourcePool path) ≤
      Scalar.classicalOperations N (repetitionCount N budget)

/-- The complete same-run scalar theorem is established for arbitrary modulus and retry target. -/
public lemma algorithm_sevenCoordinates (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path) :
    SevenCoordinateBounds N input budget path := by
  let count := Canonical.retryCount N budget
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
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .cnot)).trans_eq
      (Scalar.machine_gate_count N count .cnot)
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .singleQubit)).trans_eq
      (Scalar.machine_gate_count N count .singleQubit)
  · exact (Circuit.quantumTime_le_unitDepth _ _).trans
      ((Machine.code_depth_le pre pre_quantumWires N input count (fun _ => 1) path).trans
        (Scalar.machine_depth_scalar N count))
  · have memory := Scalar.machine_classical_coordinate N count
    exact ⟨(resident .classicalBits).trans_eq memory,
      (auxiliary .classicalBits).trans_eq memory⟩
  · exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool).trans
      (Scalar.machine_classical_operations_le N count)

/-- The unit-event chronological bound also counts all classical work and measurements. -/
public lemma algorithm_wholeRunDepth (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path) :
    (algorithm N input budget).run.code.depth (fun _ => 1) path ≤
      Scalar.wholeRunDepth N (repetitionCount N budget) :=
  (Machine.code_depth_le pre pre_quantumWires N
    input (Canonical.retryCount N budget)
    (fun _ => 1) path).trans (Scalar.machine_depth_scalar _ _)

/-- Every declared query coordinate is observed on the same original named computation. -/
public lemma algorithm_queryCount (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path)
    (coordinate : (executionModel N).OracleCoordinate) :
    ResourcePool.count (model := executionModel N) (.oracle coordinate)
      ((algorithm N input budget).run.code.resourcePool path) ≤ repetitionCount N budget := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.oracle coordinate)).trans_eq
    (Scalar.machine_query_count N (Canonical.retryCount N budget) coordinate)

/-- Preparations retain their actual positive system dimension on the original execution. -/
public lemma algorithm_preparationCount (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.preparation dimension)
      ((algorithm N input budget).run.code.resourcePool path) ≤
        if 2 = dimension then Scalar.qubits N else 0 := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.preparation dimension)).trans_eq
    (Scalar.machine_preparation_count N (Canonical.retryCount N budget) dimension)

/-- Phase and physical-reset measurements use the same full computation and dimension. -/
public lemma algorithm_measurementCount (N : Nat)
    (input : Canonical.Input N) (budget : FailureBudget)
    (path : (algorithm N input budget).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel N) (.measurement dimension)
      ((algorithm N input budget).run.code.resourcePool path) ≤
        if 2 = dimension then repetitionCount N budget * Scalar.roundMeasurements N else 0 := by
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.measurement dimension)).trans_eq
    (Scalar.machine_measurement_count N (Canonical.retryCount N budget) dimension)

/-- All seven resource coordinates and original success belong to the same named actual run. -/
public theorem main (N : Nat) (input : Canonical.Input N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    (algorithm N input budget).Solves (problem N input budget wellFormed) ∧
      (∀ path : (algorithm N input budget).run.code.Path,
        SevenCoordinateBounds N input budget path) :=
  ⟨algorithm_solves N input budget wellFormed, algorithm_sevenCoordinates N input budget⟩

end

end QuantumAlg.Factoring.ShorStyle
