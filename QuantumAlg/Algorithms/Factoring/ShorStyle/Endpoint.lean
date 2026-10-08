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
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine.Calibrated
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
public def algorithm {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) :
    Algorithm (executionModel model) pre (post model budget) (OutputShape N) :=
  Machine.algorithm pre pre_quantumWires model budget

/-- The ordinary named algorithm meets all seven obligations from every original caller. -/
public theorem algorithm_solves {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) :
    (algorithm model budget).Solves (problem model budget wellFormed) :=
  Machine.shorDeclared_machine_solves pre pre_quantumWires model budget wellFormed
    (fun _ => 1) (fun _ => rfl)

/-- The same original named run realizes its independent physically admissible full-cycle plan. -/
public def completeCycles {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    Algorithm.CycleSolves (algorithm model budget)
      (completeCycleProblem model budget wellFormed) :=
  Machine.calibratedCycleCertificate pre pre_quantumWires model budget wellFormed
    (fun _ => 1) (fun _ => rfl)

/-- The ordinary run's actual maximum cycle depth includes its first initialization. -/
public theorem completeCycles_maximumDepth_le {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) (path : (algorithm model budget).run.code.Path) :
    (completeCycles model budget wellFormed).maximumCycleDepth (fun _ => 1) path ≤
      maximumCycleDepthLimit model :=
  Machine.calibrated_maximumCycleDepth_le pre pre_quantumWires model budget wellFormed
    (fun _ => 1) (fun _ => rfl) path

/-- The original modulus and rational target internally select the genuine retry count. -/
public def repetitionCount (N : Nat) (budget : FailureBudget) : Nat :=
  Canonical.retryCount N budget

private theorem original_resident_zero : pre.residentSpace = 0 := by
  funext axis
  cases axis <;> rfl

private theorem original_auxiliary_zero : pre.auxiliarySpace = 0 := by
  funext axis
  cases axis <;> rfl

/-- Seven independent scalar observations on the same original factoring execution path. -/
@[expose] public def SevenCoordinateBounds {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed)
    (cycles : Algorithm.CycleSolves (algorithm model budget)
      (completeCycleProblem model budget wellFormed))
    (path : (algorithm model budget).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((algorithm model budget).run.code.peakResidentSpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0) ∧
    ((algorithm model budget).run.code.peakAuxiliarySpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits N else 0)) ∧
  ResourcePool.count (model := executionModel model) (.gate .toffoli)
    ((algorithm model budget).run.code.resourcePool path) ≤ 0 ∧
  ResourcePool.count (model := executionModel model) (.gate .cnot)
    ((algorithm model budget).run.code.resourcePool path) ≤
      repetitionCount N budget * Scalar.roundCnot N ∧
  ResourcePool.count (model := executionModel model) (.gate .singleQubit)
    ((algorithm model budget).run.code.resourcePool path) ≤
      repetitionCount N budget * Scalar.roundSingleQubit N ∧
  cycles.maximumCycleDepth (fun _ => 1) path ≤ Scalar.maximumCycleDepth N ∧
  (((algorithm model budget).run.code.peakResidentSpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N budget)) ∧
    ((algorithm model budget).run.code.peakAuxiliarySpace path .classicalBits ≤
      Scalar.classicalBits N (repetitionCount N budget))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm model budget).run.code.resourcePool path) ≤
      Scalar.classicalOperations N (repetitionCount N budget)

/-- The complete same-run scalar theorem is established for arbitrary modulus and retry target. -/
public theorem algorithm_sevenCoordinates {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (wellFormed : budget.WellFormed) (path : (algorithm model budget).run.code.Path) :
    SevenCoordinateBounds model budget wellFormed
      (completeCycles model budget wellFormed) path := by
  let input := Canonical.Probability.Input.ofSemiprimeModel model
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
  · have ceiling := Scalar.machine_gate_count input count .toffoli
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .toffoli)).trans_eq
      (ceiling.trans (Nat.mul_zero _))
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .cnot)).trans_eq
      (Scalar.machine_gate_count input count .cnot)
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .singleQubit)).trans_eq
      (Scalar.machine_gate_count input count .singleQubit)
  · exact (completeCycles_maximumDepth_le model budget wellFormed path).trans
      (Scalar.first_depth_scalar input)
  · have memory := Scalar.machine_classical_coordinate N count
    exact ⟨(resident .classicalBits).trans_eq memory,
      (auxiliary .classicalBits).trans_eq memory⟩
  · exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool).trans
      (Scalar.machine_classical_operations_le input count)

/-- The whole chronological bound remains separate from the maximum complete quantum cycle. -/
public theorem algorithm_wholeRunDepth {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (path : (algorithm model budget).run.code.Path) :
    (algorithm model budget).run.code.depth (fun _ => 1) path ≤
      Scalar.wholeRunDepth N (repetitionCount N budget) :=
  (Machine.code_depth_le pre pre_quantumWires N
    (Canonical.Probability.Input.ofSemiprimeModel model) (Canonical.retryCount N budget)
    (fun _ => 1) path).trans (Scalar.machine_depth_scalar _ _)

/-- Every declared query coordinate is observed on the same original named computation. -/
public theorem algorithm_queryCount {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (path : (algorithm model budget).run.code.Path)
    (coordinate : (executionModel model).OracleCoordinate) :
    ResourcePool.count (model := executionModel model) (.oracle coordinate)
      ((algorithm model budget).run.code.resourcePool path) ≤ repetitionCount N budget := by
  let input := Canonical.Probability.Input.ofSemiprimeModel model
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.oracle coordinate)).trans_eq
    (Scalar.machine_query_count input (Canonical.retryCount N budget) coordinate)

/-- Preparations retain their actual positive system dimension on the original execution. -/
public theorem algorithm_preparationCount {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (path : (algorithm model budget).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel model) (.preparation dimension)
      ((algorithm model budget).run.code.resourcePool path) ≤
        if 2 = dimension then Scalar.qubits N else 0 := by
  let input := Canonical.Probability.Input.ofSemiprimeModel model
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.preparation dimension)).trans_eq
    (Scalar.machine_preparation_count input (Canonical.retryCount N budget) dimension)

/-- Phase and physical-reset measurements use the same full computation and dimension. -/
public theorem algorithm_measurementCount {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) (budget : FailureBudget)
    (path : (algorithm model budget).run.code.Path) (dimension : ℕ+) :
    ResourcePool.count (model := executionModel model) (.measurement dimension)
      ((algorithm model budget).run.code.resourcePool path) ≤
        if 2 = dimension then repetitionCount N budget * Scalar.roundMeasurements N else 0 := by
  let input := Canonical.Probability.Input.ofSemiprimeModel model
  have pool := Machine.code_pool_le pre pre_quantumWires N input
    (Canonical.retryCount N budget) path
  exact ((ResourcePool.le_iff_count.mp pool) (.measurement dimension)).trans_eq
    (Scalar.machine_measurement_count input (Canonical.retryCount N budget) dimension)

/-- All seven resource coordinates and original success belong to the same named actual run. -/
public theorem main {N p q : Nat}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hN : N = p * q) (budget : FailureBudget) (wellFormed : budget.WellFormed) :
    ∃ cycles : Algorithm.CycleSolves
        (algorithm (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget)
        (completeCycleProblem (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget wellFormed),
      (algorithm (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget).Solves
        (problem (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget wellFormed) ∧
      (∀ path : (algorithm (semiprimeModelOfDistinctPrimes hp hq hpq hN) budget).run.code.Path,
        SevenCoordinateBounds (semiprimeModelOfDistinctPrimes hp hq hpq hN)
          budget wellFormed cycles path) :=
  ⟨completeCycles _ budget wellFormed, algorithm_solves _ budget wellFormed,
    algorithm_sevenCoordinates _ budget wellFormed⟩

end

end QuantumAlg.Factoring.ShorStyle
