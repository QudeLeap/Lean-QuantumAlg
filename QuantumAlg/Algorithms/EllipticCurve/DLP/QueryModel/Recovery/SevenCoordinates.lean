/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Cycle
public import QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.ClassicalSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.ClassicalSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.QuantumSpace
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Scalar.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Calibrated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery.Allocation
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Seven scalar coordinates of the same actual calibrated declared ECDLP path

The complete original-input algorithm has one physical cycle certificate and
seven parameter-only native ceilings. All quantum dimensions, both classical
storage roles, the actual full event ledger and the real cycle plan remain
explicit. Total chronological depth is a separate same-run observation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- Independent resource observations on one path of the complete original-input computation. -/
@[expose] public def SevenCoordinateBounds (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed)
    (cycles : Algorithm.CycleSolves (calibratedWholeAlgorithm I A expansion nontrivial budget)
      (calibratedCycleProblem I A expansion nontrivial budget wellFormed))
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.peakResidentSpace path
        (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits (fieldWidth E) (scalarWidth I) else 0) ∧
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.peakAuxiliarySpace path
        (.quantumSystems dimension) ≤
      if 2 = dimension then Scalar.qubits (fieldWidth E) (scalarWidth I) else 0)) ∧
  ResourcePool.count (model := Sampling.executionModel I A) (.gate .toffoli)
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤ 0 ∧
  ResourcePool.count (model := Sampling.executionModel I A) (.gate .cnot)
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
      retryCountForBudget I budget * Scalar.roundCnot (scalarWidth I) ∧
  ResourcePool.count (model := Sampling.executionModel I A) (.gate .singleQubit)
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
      retryCountForBudget I budget * Scalar.roundSingleQubit (fieldWidth E) (scalarWidth I) ∧
  cycles.maximumCycleDepth (fun _ => 1) path ≤
    Scalar.maximumCycleDepth (fieldWidth E) (scalarWidth I) ∧
  (((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.peakResidentSpace path
      .classicalBits ≤ Scalar.residentBits (fieldWidth E) (scalarWidth I)) ∧
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.peakAuxiliarySpace path
      .classicalBits ≤ Scalar.auxiliaryBits (fieldWidth E) (scalarWidth I))) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.resourcePool path) ≤
      retryCountForBudget I budget * Scalar.recoveryEvents (fieldWidth E) (scalarWidth I) + 1

/-- All seven scalar bounds observe the same original calibrated complete-cycle execution. -/
public theorem calibrated_sevenCoordinates (I : ECDLPInstance E) (A : Access I)
    (expansion : FiniteCyclicDLP.OrderExpansion I.subgroupOrder)
    (nontrivial : 2 ≤ (problem I).order)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed)
    (path : (calibratedWholeAlgorithm I A expansion nontrivial budget).run.code.Path) :
    SevenCoordinateBounds I A expansion nontrivial budget wellFormed
      (calibratedCycleCertificate I A expansion nontrivial budget wellFormed) path := by
  have pool := ecdlpRecovery_code_events_le I A expansion nontrivial
    (retryCountForBudget I budget) path
  have resident := ecdlpRecovery_code_resident_le I A expansion nontrivial
    (retryCountForBudget I budget) path
  have auxiliary := ecdlpRecovery_code_auxiliary_le I A expansion nontrivial
    (retryCountForBudget I budget) path
  unfold SevenCoordinateBounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    have quantum := whole_memory_quantum_coordinates I dimension
    rw [original_qubits_scalar] at quantum
    exact ⟨(resident (.quantumSystems dimension)).trans_eq quantum.1,
      (auxiliary (.quantumSystems dimension)).trans_eq quantum.2⟩
  · have ceiling := whole_budget_gate_scalar I A expansion nontrivial
      (retryCountForBudget I budget) .toffoli
    exact ((ResourcePool.le_iff_count.mp pool) (.gate .toffoli)).trans
      (ceiling.trans_eq (Nat.mul_zero _))
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .cnot)).trans
      (whole_budget_gate_scalar I A expansion nontrivial (retryCountForBudget I budget) .cnot)
  · exact ((ResourcePool.le_iff_count.mp pool) (.gate .singleQubit)).trans
      (whole_budget_gate_scalar I A expansion nontrivial
        (retryCountForBudget I budget) .singleQubit)
  · exact calibrated_maximumCycleDepth_scalar I A expansion nontrivial budget wellFormed path
  · exact ⟨(resident .classicalBits).trans (whole_memory_classical_scalar I).1,
      (auxiliary .classicalBits).trans (whole_memory_classical_scalar I).2⟩
  · exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight pool).trans
      (whole_budget_classical_scalar I A expansion nontrivial (retryCountForBudget I budget))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
