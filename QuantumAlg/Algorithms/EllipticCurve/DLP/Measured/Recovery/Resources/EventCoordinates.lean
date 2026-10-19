/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Resources.Events
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation.Events
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Resources
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Coordinates
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import Mathlib.Tactic.Ring

/-!
# Native coordinates and unit-duration depth of the same actual recovery

The complete independent event budget pays for the five first preparations,
every actual reset and converted sampler, the original native checked attempt,
and one final paid option pack. Quantum selection preserves gate multiplicity;
native checking and final packing add only classical-operation coordinates.

The round cardinality identity is a polynomial identity for every natural
field and sample width, including zero. It uses no truncated subtraction or
positive-width premise. Whole-run unit-duration depth is bounded from the same
actual Path and complete pool, independently of the quantum-time coordinate.

-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.EventCoordinates

noncomputable section

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

private lemma unitWeight_card {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.weightedCount (fun _ => 1) pool = pool.card := by
  simp only [ResourcePool.weightedCount, Multiset.map_const', Multiset.sum_replicate,
    Nat.nsmul_eq_mul, Nat.mul_one]

/-- The three gate coordinates and all actual sampler/reset measurements are retained. -/
lemma roundBudget_card (width m : Nat) :
    (Events.roundBudget width m).card =
      LogicalResources.Scalar.roundToffoli width m +
        LogicalResources.Scalar.roundCnot width m +
        LogicalResources.Scalar.roundSingle width m +
        2 * m * (2 * width + 1) + Recovery.PublicInput.Allocation.Events.bankWidth width := by
  simp [Events.roundBudget, Recovery.Conversion.Events.gateBudget,
    Recovery.Conversion.Events.toffoli, Recovery.Conversion.Events.cnot,
    Recovery.Conversion.Events.single, Recovery.Conversion.Events.measured,
    Recovery.Stage.Events.cnot, Recovery.Stage.Events.single, Recovery.Stage.Events.measured,
    ResourcePool.singleton, Multiset.card_nsmul]

/-- Natural-number equality for all widths, without subtraction or a nonzero-width premise. -/
lemma roundBudget_card_balance (width m : Nat) :
    (Events.roundBudget width m).card + 2 * m =
      LogicalResources.Scalar.roundEvents width m + 2 := by
  rw [roundBudget_card]
  unfold Recovery.PublicInput.Allocation.Events.bankWidth
    LogicalResources.Scalar.roundToffoli LogicalResources.Scalar.roundCnot
    LogicalResources.Scalar.roundSingle LogicalResources.Scalar.roundEvents
    LogicalResources.Scalar.qubits LogicalResources.Scalar.multiplierEvents
    LogicalResources.Scalar.multiplierCnot LogicalResources.Scalar.pointToffoli
    LogicalResources.Scalar.pointCnot LogicalResources.Scalar.pointSingle
    LogicalResources.Scalar.pointEvents
  ring

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (problem : KnownOrderProblem E.GroupPoint)

/-- Native checking and packing contribute no gate; initialization is preparation only. -/
lemma fullBudget_gate_count (nontrivial : 2 ≤ problem.order) (count : Nat)
    (gate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate gate)
        (Events.fullBudget E problem nontrivial count) =
      count * ResourcePool.count (model := Events.QuantumModel) (.gate gate)
        (Recovery.Conversion.Events.gateBudget p.size (orderWidth problem)) := by
  have native := attemptEnvelope_count_eq_zero (model := Model) (.gate gate)
    (fun label equality => by cases equality) (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
  simp only [Events.fullBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
    ResourcePool.count_add, ResourcePool.count_scale, native,
    BitWord.liftQuantumPool_gate_count, Events.roundBudget,
    Recovery.PublicInput.Allocation.Events.allocationBudget,
    Recovery.PublicInput.Allocation.Events.preparation, ResourcePool.count_nsmul,
    ResourcePool.count_singleton, reduceCtorEq, ↓reduceIte, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero]
  simp [ResourcePool.ofList, ResourcePool.count]

/-- Complete independent event cardinality includes allocation and packing even at count zero. -/
lemma fullBudget_card_le (nontrivial : 2 ≤ problem.order) (count : Nat) :
    (Events.fullBudget E problem nontrivial count).card ≤
      Recovery.PublicInput.Allocation.Events.bankWidth p.size +
        count * ((Events.roundBudget p.size (orderWidth problem)).card +
          LogicalResources.Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E)
            (orderWidth problem)) + 1 := by
  have native :
      (attemptEnvelope Model (ECDLP.Canonical.Layout.curveSpec E)
        (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)).card ≤
      LogicalResources.Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth problem) :=
    attemptEnvelope_card_le Model (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
  calc
    _ = Recovery.PublicInput.Allocation.Events.bankWidth p.size +
        count * ((Events.roundBudget p.size (orderWidth problem)).card +
          (attemptEnvelope Model (ECDLP.Canonical.Layout.curveSpec E)
            (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)).card) + 1 := by
      simp [Events.fullBudget, sampledRecoveryEnvelope, sampledAttemptsEnvelope,
        ResourcePool.scale, BitWord.liftQuantumPool_card,
        Recovery.PublicInput.Allocation.Events.allocationBudget,
        Recovery.PublicInput.Allocation.Events.preparation, ResourcePool.singleton,
        ResourcePool.ofList, Multiset.card_nsmul, Nat.mul_add, Nat.add_assoc]
    _ ≤ _ := Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.mul_le_mul_left count (Nat.add_le_add_left native _)) _) 1

variable [Fact p.Prime] (fieldTail : Nat)
  (points : Fin (2 * orderWidth problem) → AffinePoint E)
  (seed : AffinePoint E) (r : Nat) (coefficient : (ZMod p)ˣ)
  (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Every actual full Path inherits each native gate ceiling from the independent full pool. -/
lemma run_gate_count_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path)
    (gate : AlgorithmGate.Coordinate) :
    ResourcePool.count (model := Model) (.gate gate)
        ((run E fieldTail problem points seed r coefficient nontrivial count).code.resourcePool
          path) ≤
      count * ResourcePool.count (model := Events.QuantumModel) (.gate gate)
        (Recovery.Conversion.Events.gateBudget p.size (orderWidth problem)) :=
  (ResourcePool.le_iff_count.mp
    (Events.run_budget E fieldTail problem points seed r coefficient nontrivial count path)
      (Resource.Event.gate (model := Model) gate)).trans_eq
    (fullBudget_gate_count E problem nontrivial count gate)

/-- Independent unit-duration depth observes the same complete Path and pays every event kind. -/
lemma run_unitDepth_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.depth
        (fun _ => 1) path ≤
      (Events.fullBudget E problem nontrivial count).card := by
  have bounded := Circuit.depth_le_weightedCount_of_pool_le
    (run E fieldTail problem points seed r coefficient nontrivial count).code (fun _ => 1)
    (Events.fullBudget E problem nontrivial count) path
    (Events.run_budget E fieldTail problem points seed r coefficient nontrivial count path)
  simpa only [unitWeight_card] using bounded

end

end ExecutionContract.EventCoordinates
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
