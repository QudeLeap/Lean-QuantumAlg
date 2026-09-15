/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources.Recovery
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Resources.Classical
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Cardinality

/-!
# Complete native classical-operation bound for ECDLP

The original literal unitary, finite measurements and paid reset shifts have
no classical-operation label. Every real checked attempt is bounded by its
original complete native envelope, and the final optional-result pack adds
one operation. The independent envelope is used only for an upper bound on
the same complete recovery path, including count zero.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native
open FiniteCyclicDLP.Canonical

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem classical_list (events : List (Resource.Event .quantum)) :
    classicalOperationCard (ResourcePool.ofList events) = events.countP isClassicalOperation := by
  change events.countP (fun event => decide (isClassicalOperation event = true)) = _
  congr 1
  funext event
  cases isClassicalOperation event <;> rfl

private theorem orderEnvelope_classical_zero {order : Nat} (B : OrderExpansion order) :
    classicalOperationCard (GateLevelResources.orderPreparationEnvelope B) = 0 := by
  simp [GateLevelResources.orderPreparationEnvelope,
    UniformSuperposition.rotationYEvent_eq_gate, UniformSuperposition.cnotEvent_eq_gate,
    classicalOperationCard_singleton_nonClassical]

private theorem sampleEnvelope_classical_zero (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    classicalOperationCard (sampleEnvelope I B) = 0 := by
  simp [sampleEnvelope, unitaryEnvelope, orderEnvelope_classical_zero,
    classicalOperationCard_singleton_nonClassical,
    uPQEvent, Circuit.zEvent]

private theorem resetStage_classical_zero (dimension : ℕ+) (value : Fin dimension) :
    classicalOperationCard (resetStageEnvelope dimension value) = 0 := by
  rw [resetStageEnvelope, classicalOperationCard_add, classicalOperationCard_add]
  simp [classicalOperationCard_singleton_nonClassical, classical_list,
    List.countP_eq_zero, List.mem_ofFn, isClassicalOperation, Circuit.zEvent]

private theorem resetEnvelope_classical_zero (I : ECDLPInstance E) :
    classicalOperationCard (resetEnvelope I) = 0 := by
  unfold resetEnvelope
  induction (Finset.univ : Finset (Fin (Layout.totalQubits I))) using Finset.induction_on with
  | empty => simp
  | @insert index indices fresh ih =>
      erw [Finset.sum_insert fresh, classicalOperationCard_add,
        resetStage_classical_zero, ih, zero_add]

private theorem reusedEnvelope_classical_zero (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) :
    classicalOperationCard (reusedSampleEnvelope I B) = 0 := by
  rw [reusedSampleEnvelope, classicalOperationCard_add,
    resetEnvelope_classical_zero, sampleEnvelope_classical_zero, add_zero]

/-- Literal member execution and actual finite readouts perform no classical operation. -/
theorem nativeECDLP_sample_classicalOperationCard_zero
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I)
    (path : (sample base noQuantum I B A).Path) :
    classicalOperationCard ((sample base noQuantum I B A).resourcePool path) = 0 := by
  rw [Circuit.resourcePool, nativeECDLP_sample_eventTrace, ResourcePool.ofList_append,
    classicalOperationCard_add, UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    GateLevelResources.quantumCircuit_classicalOperationCard_zero, zero_add]
  simp [classical_list, List.countP_replicate, isClassicalOperation, Circuit.zEvent]

/-- The independent complete event allowance has the original checked-operation ceiling. -/
theorem nativeECDLP_recoveryEnvelope_classicalOperationCard_le
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (count : Nat) :
    classicalOperationCard (recoveryEnvelope I B count) ≤
      count * (42 * FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) * (248 * Layout.fieldWidth E + 644) + 119) + 1 := by
  have attempt := (Multiset.countP_le_card
    (p := fun event : Resource.Event .quantum => isClassicalOperation event)
    (attemptEnvelope .quantum (Layout.curveSpec E) (recoveryModulus I))).trans
      (attemptEnvelope_card_le .quantum (Layout.curveSpec E) (recoveryModulus I))
  have initial : classicalOperationCard (ResourcePool.singleton (preparation I).event) = 0 := by
    exact classicalOperationCard_singleton_nonClassical _
      (fun label equality => by cases equality) 1
  rw [recoveryEnvelope, classicalOperationCard_add, initial, zero_add,
    sampledRecoveryEnvelope, classicalOperationCard_add, sampledAttemptsEnvelope,
    classicalOperationCard_scale, classicalOperationCard_add, reusedEnvelope_classical_zero,
    zero_add]
  have finalPack : classicalOperationCard (ResourcePool.ofList
      [.classicalOperation (.nominalEncoding
        (.packOption (FiniteCyclicDLP.orderWidth (problem I))))]) = 1 := by
    simp
  rw [finalPack]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left count attempt) 1

attribute [local irreducible] underPersistent

/-- Every actual path includes all checked recovery instructions and the one final pack. -/
theorem nativeECDLP_recovery_classicalOperationCard_le
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    classicalOperationCard
      ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path) ≤
      count * (42 * FiniteCyclicDLP.orderWidth (problem I) +
        FiniteCyclicDLP.orderWidth (problem I) * (248 * Layout.fieldWidth E + 644) + 119) + 1 := by
  exact (Multiset.countP_le_of_le (p := fun event => isClassicalOperation event)
    (nativeECDLP_recovery_pool_le base noQuantum I B A count basePoint targetPoint path)).trans
      (nativeECDLP_recoveryEnvelope_classicalOperationCard_le I B count)

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
