/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
public import QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits
public import QuantumAlg.Core.Base.Accounting.Weighted
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Space

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.EventCoordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.ActualRun
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Execution
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Time
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation.Events
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Seed
import all QuantumAlg.Algorithms.EllipticCurve.P256.Resources.Limits

/-!
# Seven numeric P-256 ceilings with the reduced quantum bank and independent unit-duration depth

Every bound concerns the named P-256 algorithm and every complete actual Path.
The seven coordinates use the reduced 818-qubit bank in both storage roles
and every quantum dimension, together with the six independent numerical
limits for native gates, quantum time, classical storage and classical work.

Unit-duration whole-run depth is proved separately from quantum time. Five
initial prepareZero instructions cost 818 events, every converted/reset round
retains all gate and measurement occurrences, native checking has its original
ceiling, and the final option pack costs one. The exact independent cardinality
comparison leaves 2441641 events of the original whole-run allowance unused.
No success, support, caller resource certificate or initial cleanliness premise
is needed.
-/

namespace QuantumAlg.EllipticCurve.P256.StreamingResources

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.ExecutionContract

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.GenericPointAddition.InPlace
open FiniteCyclicDLP

attribute [local irreducible] run

/-- The reduced-bank seven independent numerical coordinates on one complete actual P-256 Path. -/
@[expose] public def SevenCoordinateBounds (I : P256.DomainParameters.PublicKeyInstance)
    (path : (P256.ActualRun.algorithm I).run.code.Path) : Prop :=
  (∀ dimension : ℕ+,
    SpacePool.count (.quantumSystems dimension)
        ((P256.ActualRun.algorithm I).run.code.peakResidentSpace path) ≤
        (if 2 = dimension then 818 else 0) ∧
      SpacePool.count (.quantumSystems dimension)
        ((P256.ActualRun.algorithm I).run.code.peakAuxiliarySpace path) ≤
        (if 2 = dimension then 818 else 0)) ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .toffoli)
      ((P256.ActualRun.algorithm I).run.code.resourcePool path) ≤
        P256LogicalResources.Limits.toffoli ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model) (.gate .cnot)
      ((P256.ActualRun.algorithm I).run.code.resourcePool path) ≤ P256LogicalResources.Limits.cnot ∧
  ResourcePool.count (model := .quantum AlgorithmGate.model .empty BitWord.model)
      (.gate .singleQubit) ((P256.ActualRun.algorithm I).run.code.resourcePool path) ≤
        P256LogicalResources.Limits.singleQubit ∧
  (P256.ActualRun.algorithm I).run.code.quantumTime path ≤ P256LogicalResources.Limits.quantumTime ∧
  (SpacePool.count .classicalBits ((P256.ActualRun.algorithm I).run.code.peakResidentSpace path) ≤
        P256LogicalResources.Limits.residentBits ∧
      SpacePool.count .classicalBits
        ((P256.ActualRun.algorithm I).run.code.peakAuxiliarySpace path) ≤
        P256LogicalResources.Limits.auxiliaryBits) ∧
  ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((P256.ActualRun.algorithm I).run.code.resourcePool path) ≤
        P256LogicalResources.Limits.classicalOperations

section NumericSubstitution

attribute [local irreducible] Nat.size Nat.clog

/-- The reduced bank and six remaining numerical ceilings hold together for the same complete
actual Path. -/
lemma run_sevenCoordinates (I : P256.DomainParameters.PublicKeyInstance)
    (path : (P256.ActualRun.algorithm I).run.code.Path) : SevenCoordinateBounds I path := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have gateBound := EventCoordinates.run_gate_count_le
    (P256.DomainParameters.curve I.curveCert)
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)) 255
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert)) I.subgroupCert.prime.two_le 4714 path
  have classical := Coordinates.run_classical_space_scalar_le
    (P256.DomainParameters.curve I.curveCert) 255
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert)) I.subgroupCert.prime.two_le 4714 path
  have native := Coordinates.run_classicalOperations_le
    (P256.DomainParameters.curve I.curveCert) 255
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert)) I.subgroupCert.prime.two_le 4714 path
  refine ⟨?_, ?_, ?_, ?_, P256.StreamingResources.Time.run_quantumTime_le I path, ?_, ?_⟩
  · intro dimension
    exact P256.StreamingResources.Coordinates.run_quantumSystems_le I path dimension
  · apply (gateBound .toffoli).trans_eq
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_toffoli_count,
      P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
      P256LogicalResources.Limits.toffoli_eq]
  · apply (gateBound .cnot).trans_eq
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_cnot_count,
      P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
      P256LogicalResources.Limits.cnot_eq]
  · apply (gateBound .singleQubit).trans
    rw [ECDLP.Measured.Recovery.Conversion.Events.gateBudget_single_count,
      P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260]
    exact (Nat.le_add_left (4714 * LogicalResources.Scalar.roundSingle 256 260)
      (LogicalResources.Scalar.loadBits 256)).trans_eq P256LogicalResources.Limits.singleQubit_eq
  · refine ⟨classical.1.trans_eq ?_, classical.2.trans_eq ?_⟩
    · rw [P256.Measured.fieldModulus_size, P256.Measured.canonicalFieldWidth,
        P256.Measured.orderWidth_eq_260, P256LogicalResources.Limits.residentBits_eq]
    · rw [P256.Measured.fieldModulus_size, P256.Measured.canonicalFieldWidth,
        P256.Measured.orderWidth_eq_260, P256LogicalResources.Limits.auxiliaryBits_eq]
  · apply native.trans_eq
    rw [P256.Measured.canonicalFieldWidth, P256.Measured.orderWidth_eq_260,
      P256LogicalResources.Limits.classicalOperations_eq]

end NumericSubstitution

private lemma cardinality_margin_of_balance (bank initial round native original : Nat)
    (bank_eq : bank = 818) (initial_eq : initial = 607)
    (balance : round + 2 * 260 = original + 2) :
    bank + 4714 * (round + native) + 1 + 2441641 =
      initial + 4714 * (original + native) + 1 := by omega

private lemma independent_cardinality_margin :
    ECDLP.Measured.Recovery.PublicInput.Allocation.Events.bankWidth 256 +
        4714 * ((Events.roundBudget 256 260).card +
          LogicalResources.Scalar.recoveryEvents 256 260) + 1 + 2441641 =
      LogicalResources.Scalar.wholeRunEvents 256 256 260 4714 := by
  exact cardinality_margin_of_balance _ _ _ _ _ (by decide) (by decide)
    (EventCoordinates.roundBudget_card_balance 256 260)

/-- The independent complete pool fits the original numeric depth allowance with every event. -/
lemma fullBudget_card_le (I : P256.DomainParameters.PublicKeyInstance) :
    (Events.fullBudget (P256.DomainParameters.curve I.curveCert)
      (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
      I.subgroupCert.prime.two_le 4714).card ≤ P256LogicalResources.Limits.wholeRunDepth := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  have bounded := EventCoordinates.fullBudget_card_le
    (P256.DomainParameters.curve I.curveCert)
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le 4714
  rw [P256.Measured.fieldModulus_size, P256.Measured.orderWidth_eq_260,
    P256.Measured.canonicalFieldWidth] at bounded
  have independent : ECDLP.Measured.Recovery.PublicInput.Allocation.Events.bankWidth 256 +
        4714 * ((Events.roundBudget 256 260).card +
          LogicalResources.Scalar.recoveryEvents 256 260) + 1 ≤
      LogicalResources.Scalar.wholeRunEvents 256 256 260 4714 :=
    (Nat.le_add_right _ 2441641).trans_eq independent_cardinality_margin
  exact (bounded.trans independent).trans_eq P256LogicalResources.Limits.wholeRunDepth_eq

/-- Independent unit-duration depth bounds the entire same actual run, on every full Path. -/
lemma run_wholeRunDepth_le (I : P256.DomainParameters.PublicKeyInstance)
    (path : (P256.ActualRun.algorithm I).run.code.Path) :
    (P256.ActualRun.algorithm I).run.code.depth (fun _ => 1) path ≤
      P256LogicalResources.Limits.wholeRunDepth := by
  have : Fact P256.DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact (EventCoordinates.run_unitDepth_le (P256.DomainParameters.curve I.curveCert)
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I)) 255
    (P256.Cascade.addend I) (P256.Measured.fixedSeed I) P256.DomainParameters.subgroupOrder
    (Semantics.radixUnit P256.DomainParameters.fieldModulus (Nat.succ 255)
      (P256.Measured.fieldModulus_odd I.curveCert)) I.subgroupCert.prime.two_le 4714 path).trans
      (fullBudget_card_le I)

end

end QuantumAlg.EllipticCurve.P256.StreamingResources
