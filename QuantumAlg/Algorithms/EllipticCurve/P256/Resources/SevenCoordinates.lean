/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Cycle
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Cycle
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Solves
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Repetition
import all QuantumAlg.Algorithms.EllipticCurve.Resources

/-!
# Complete P-256 resources by specialization of the generic public theorem

Success, state, joint borrowed restoration, physically complete cycles and
every resource coordinate refer to the original named actual execution.
Only standard parameter facts and scalar arithmetic specialize the generic
contract [PZ03, ecc.tex:448-556]. The original exceptional-mass and finite
repetition calibration is unchanged.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

/-- All seven independent numeric resource coordinates on one actual P-256 path.
Both storage roles and every quantum dimension are retained. -/
@[expose] public def SevenCoordinateBounds (I : P256.DomainParameters.PublicKeyInstance)
    (cycles : Algorithm.CycleSolves (algorithm I) (completeCycleProblem I))
    (path : (algorithm I).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    ((algorithm I).run.code.peakResidentSpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Limits.qubits else 0) ∧
    ((algorithm I).run.code.peakAuxiliarySpace path (.quantumSystems dimension) ≤
      if 2 = dimension then Limits.qubits else 0)) ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (.gate .toffoli) ((algorithm I).run.code.resourcePool path) ≤ Limits.toffoli ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (.gate .cnot) ((algorithm I).run.code.resourcePool path) ≤ Limits.cnot ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
    (.gate .singleQubit) ((algorithm I).run.code.resourcePool path) ≤ Limits.singleQubit ∧
  cycles.maximumCycleDepth (fun _ => 1) path ≤ Limits.maximumCycleDepth ∧
  (((algorithm I).run.code.peakResidentSpace path .classicalBits ≤ Limits.residentBits) ∧
    ((algorithm I).run.code.peakAuxiliarySpace path .classicalBits ≤ Limits.auxiliaryBits)) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
    ((algorithm I).run.code.resourcePool path) ≤ Limits.classicalOperations

/-- Direct application of the complete generic main to the original fixed run. -/
theorem algorithm_completeContract (I : P256.DomainParameters.PublicKeyInstance) :
    ∃ cycles : Algorithm.CycleSolves (algorithm I) (completeCycleProblem I),
      (algorithm I).Solves (problem I) ∧
        (∀ path : (algorithm I).run.code.Path, SevenCoordinateBounds I cycles path) ∧
        (∀ path : (algorithm I).run.code.Path,
          (algorithm I).run.code.depth (fun _ => 1) path ≤ Limits.wholeRunDepth) := by
  let : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  rcases LogicalResources.main (P256.DomainParameters.curve I.curveCert) 255
      P256.Measured.fieldTail_sameWidth P256.Measured.fieldTail_fits
      (P256.Measured.fieldModulus_odd I.curveCert) (P256.Cascade.ecdlpInstance I)
      (P256.Cascade.addend I) (P256.Measured.fixedSeed I)
      (P256.Measured.addend_original_encoding I) 4714 ((1 : ℝ) / 100)
      (P256.Measured.repetitionCondition I) with ⟨cycles, correct, coordinates, wholeRun⟩
  have coordinateWidth : Nat.clog 2 P256.DomainParameters.fieldModulus = 256 := by
    rw [P256.DomainParameters.fieldModulus_eq_primeModulus]
    exact P256.DomainParameters.fieldWidth_eq_256
  refine ⟨cycles, correct, ?_, ?_⟩
  · intro path
    rcases coordinates path with
      ⟨qubits, toffoli, cnot, singleQubit, cycleDepth, classicalBits, classicalOperations⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro dimension
      refine ⟨Nat.le_trans (qubits dimension).1 ?_, Nat.le_trans (qubits dimension).2 ?_⟩
      all_goals
        rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
          Limits.qubits_eq]
    · refine Nat.le_trans toffoli ?_
      rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
        Limits.toffoli_eq]
    · refine Nat.le_trans cnot ?_
      rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
        Limits.cnot_eq]
    · refine Nat.le_trans singleQubit ?_
      rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
        Limits.singleQubit_eq]
    · refine Nat.le_trans cycleDepth ?_
      rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
        coordinateWidth, Limits.maximumCycleDepth_eq]
    · refine ⟨Nat.le_trans classicalBits.1 ?_, Nat.le_trans classicalBits.2 ?_⟩
      · rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
          coordinateWidth, Limits.residentBits_eq]
      · rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
          coordinateWidth, Limits.auxiliaryBits_eq]
    · refine Nat.le_trans classicalOperations ?_
      rw [P256.Measured.orderWidth_eq_260, coordinateWidth, Limits.classicalOperations_eq]
  · intro path
    refine Nat.le_trans (wholeRun path) ?_
    rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
      coordinateWidth, Limits.wholeRunDepth_eq]

end

end QuantumAlg.EllipticCurve.P256LogicalResources
