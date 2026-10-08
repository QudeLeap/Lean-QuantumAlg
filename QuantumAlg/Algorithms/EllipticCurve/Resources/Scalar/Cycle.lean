/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.FullRun
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Cycle.Complete

/-! # Closed-form depth ceiling for the actual complete generic ECC cycle plan -/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured ScalarMultiplication.MeasuredPlacement

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)
  (known : KnownOrderProblem E.GroupPoint) (nontrivial : 2 ≤ known.order)

private theorem checkedSectionDepth_scalar_le :
    checkedSectionDepthBudget E known nontrivial ≤
      Scalar.roundEvents p.size (orderWidth known) +
        Scalar.recoveryEvents (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth known) +
        2 * Scalar.qubits p.size (orderWidth known) := by
  rw [checkedSectionDepthBudget, scalar_unitWeight_card]
  simp only [checkedSectionEventBudget, Multiset.card_add, BitWord.liftQuantumPool_card]
  rw [samplingResetBudget_card, terminal_systemCount_scalar]
  exact Nat.add_le_add_right
    (Nat.add_le_add (samplingRound_events_scalar E known)
      (recoveryAttempt_events_scalar E known nontrivial)) _

private theorem initializedDepth_scalar_le :
    initializedRepeatedDepthBudget E known nontrivial ≤
      Scalar.maximumCycleDepth p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth known) := by
  unfold initializedRepeatedDepthBudget
  apply max_le
  · rw [scalar_unitWeight_card]
    simp only [initializedFirstCheckedSectionEventBudget, Multiset.card_add,
      BitWord.liftQuantumPool_card, ResourcePool.ofList, Multiset.coe_card]
    have first := initializationTrace_length_scalar p (2 * orderWidth known)
    have sectionBound := checkedSectionDepth_scalar_le E known nontrivial
    rw [checkedSectionDepthBudget, scalar_unitWeight_card] at sectionBound
    unfold Scalar.maximumCycleDepth
    omega
  · have sectionBound := checkedSectionDepth_scalar_le E known nontrivial
    unfold Scalar.maximumCycleDepth
    omega

variable (I : ECDLPInstance E)

/-- Zero and one retain their actual whole computation; all other counts use
the physically completed initialized/reused/terminal plan's symbolic maximum. -/
theorem completeCycleDepth_scalar_le :
    completeCycleDepthBudget E I ≤
      Scalar.maximumCycleDepth p.size (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) := by
  unfold completeCycleDepthBudget
  apply max_le
  · rw [depthLimit, scalar_unitWeight_card]
    have total := repeatedRun_events_scalar E (ECDLP.Canonical.problem I)
      I.subgroupOrder_prime.two_le 0
    unfold Scalar.wholeRunEvents Scalar.maximumCycleDepth at *
    omega
  · apply max_le
    · rw [depthLimit, scalar_unitWeight_card]
      have total := repeatedRun_events_scalar E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le 1
      unfold Scalar.wholeRunEvents Scalar.maximumCycleDepth at *
      omega
    · exact initializedDepth_scalar_le E (ECDLP.Canonical.problem I)
        I.subgroupOrder_prime.two_le

end

end QuantumAlg.EllipticCurve.LogicalResources
