/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Checked
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Space
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Cardinality

/-!
# Resources of the same complete checked quantum execution

The original quantum sample feeds its actual checked recovery once. Its
preparations, every measurement, the full original recovery and elliptic
curve verification, first-accepted selection and final option packing are
charged on the same path. All quantum wires and both public points remain
resident beside the actual persistent destinations and lexical scratch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP Canonical.Probability
open ScalarMultiplication.MeasuredPlacement ConcreteCircuitAccess
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- Every actual native event is covered by the original sample and complete recovery budgets. -/
theorem exponentCheckedRun_budget (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (path : (exponentCheckedRun E fieldTail odd problem points nontrivial).code.Path) :
    (exponentCheckedRun E fieldTail odd problem points nontrivial).code.resourcePool path ≤
      ((exponentPreparationCircuit problem).eventCost +
        Encoding.convertedEventBudget p (2 * orderWidth problem) (2 * orderWidth problem) +
          (exponentReadoutCircuit problem).eventCost +
            (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2)) +
        recoveryTailEnvelope .quantum (Canonical.Layout.curveSpec E)
          (recoveryModulusSpec problem nontrivial) 1 := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (PublicInput.exponentRun_budget E fieldTail odd problem points path.1)
    (recoveryTail_pool_le (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) _ _ _ path.2)

/-- Recovery follows the original quantum path and includes the final option-pack duration. -/
theorem exponentCheckedRun_duration (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (duration : Resource.Event .quantum → Nat)
    (path : (exponentCheckedRun E fieldTail odd problem points nontrivial).code.Path) :
    (exponentCheckedRun E fieldTail odd problem points nontrivial).code.depth duration path ≤
      (PublicInput.exponentRun E fieldTail odd problem points).code.depth duration path.1 +
        attemptDepthLimit (Canonical.Layout.curveSpec E)
          (recoveryModulusSpec problem nontrivial) duration +
        duration (.classicalOperation (.nominalEncoding (.packOption (orderWidth problem)))) := by
  change (PublicInput.exponentRun E fieldTail odd problem points).code.depth duration path.1 +
    _ ≤ _
  have recovery := recoveryTail_depth_le (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) _ _ _ duration path.2
  simp only [one_mul] at recovery
  exact (Nat.add_le_add_left recovery _).trans_eq (Nat.add_assoc _ _ _).symm

/-- A serial unit-duration bound accounts for all actual quantum and classical stages. -/
theorem exponentCheckedRun_depth (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (path : (exponentCheckedRun E fieldTail odd problem points nontrivial).code.Path) :
    (exponentCheckedRun E fieldTail odd problem points nontrivial).code.depth (fun _ => 1) path ≤
      ((exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
        (2 + (4 * MAU.Multiplication.Gidney.eventBound p.size +
          (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size)) +
        (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
          2 * orderWidth problem) +
        attemptDepthLimit (kind := .quantum) (Canonical.Layout.curveSpec E)
          (recoveryModulusSpec problem nontrivial) (fun _ => 1) + 1 :=
  (exponentCheckedRun_duration E fieldTail odd problem points nontrivial (fun _ => 1) path).trans
    (Nat.add_le_add_right (Nat.add_le_add_right
      (PublicInput.exponentRun_depth E fieldTail odd problem points path.1) _) 1)

/-- Actual recovery storage stays beside every original quantum system and public input. -/
theorem exponentCheckedRun_resident (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (path : (exponentCheckedRun E fieldTail odd problem points nontrivial).code.Path) :
    (exponentCheckedRun E fieldTail odd problem points nontrivial).code.peakResidentSpace path ≤
      (recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
        persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem)) +
      ((2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem) +
          2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E)) := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [PublicInput.exponentRun_resident]
    exact fun _ => Nat.le_add_left _ _
  · have recovery := recoveryTail_resident_le (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) _ _ _ path.2
    simp only [PublicInput.terminal, RuntimeCtx.residentSpace_disjointUnion,
      exponentMeasurementContext_resident, Allocation.after_resident,
      PublicInput.frame_resident] at recovery
    exact recovery

/-- The same auxiliary allowance counts retained results and preserves borrowed roles. -/
theorem exponentCheckedRun_auxiliary (fieldTail : Nat) (odd : Odd p)
    (problem : KnownOrderProblem E.GroupPoint)
    (points : Fin (2 * orderWidth problem) → AffinePoint E) (nontrivial : 2 ≤ problem.order)
    (path : (exponentCheckedRun E fieldTail odd problem points nontrivial).code.Path) :
    (exponentCheckedRun E fieldTail odd problem points nontrivial).code.peakAuxiliarySpace path ≤
      (recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
        persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem)) +
      ((2 * orderWidth problem) • SpacePool.ofShape (.finite 2) +
        readySpace p.size (2 * orderWidth problem)) := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [PublicInput.exponentRun_auxiliary]
    exact fun _ => Nat.le_add_left _ _
  · have recovery := recoveryTail_auxiliary_le (Canonical.Layout.curveSpec E)
      (recoveryModulusSpec problem nontrivial) _ _ _ path.2
    simp only [PublicInput.terminal, RuntimeCtx.auxiliarySpace_disjointUnion,
      exponentMeasurementContext_auxiliary, Allocation.after_auxiliary,
      PublicInput.frame_auxiliary, add_zero] at recovery
    exact recovery

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
