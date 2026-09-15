/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.RoundResources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Space
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources

/-!
# Complete actual repeated ECDLP resource bounds

The original two preparations and terminal storage allocation occur once.
Every round then performs actual reset, sampling, terminal readout and complete
classical checked recovery using the same workspace and seven persistent
cells. The final optional result is allocated and packed once, including at
count zero. These bounds charge all native classical instructions and retain
both public point inputs. Only time and event allowances scale with count;
no quantum or classical resident bank is multiplied by the repetition count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP GenericPointAddition.InPlace MeasuredUncompute
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- Preparations occur once; all reset, quantum, classical and final-pack events are charged. -/
def repeatedRunBudget : ResourcePool .quantum :=
  ResourcePool.ofList [(InPlacePreparation.preparation p).event,
    (BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).event] +
      sampledRecoveryEnvelope .quantum
        (samplingRoundBudget E fieldTail sameWidth fits problem seed)
        (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) count

/-- Only event and serial-time allowances scale by the number of actual rounds. -/
theorem exponentRepeatedRun_pool_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.resourcePool path ≤
        repeatedRunBudget E fieldTail sameWidth fits problem seed nontrivial count := by
  change ResourcePool.ofList
    (((PublicInput.initializeWork E (orderWidth problem)).eventTrace path.1.1 ++
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.1.2) ++ _) ≤ _
  have noEvents :
      (PublicInput.allocateTerminal E (orderWidth problem)).eventTrace path.1.2 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [noEvents, List.append_nil, ResourcePool.ofList_append, PublicInput.initializeWork_eventTrace]
  exact add_le_add le_rfl
    (sampledRecoveryTail_pool_le
      (samplingRound E fieldTail sameWidth fits odd problem points seed)
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _
      (samplingRoundBudget E fieldTail sameWidth fits problem seed)
      (samplingRound_pool_le E fieldTail sameWidth fits odd problem points seed) path.2)

/-- The original preparation durations precede the same actual sampled-recovery tail path. -/
theorem exponentRepeatedRun_duration (duration : Resource.Event .quantum → Nat)
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.depth duration path =
        duration (InPlacePreparation.preparation p).event +
          duration (BasisPreparation.zero (indexedLayout p.size (2 * orderWidth problem))).event +
        (sampledRecoveryTail
          (samplingRound E fieldTail sameWidth fits odd problem points seed)
          (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
          (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
          (rawRecoveryInput problem
            (inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
              (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))))
          (PublicInput.terminalBaseRef E (orderWidth problem))
          (PublicInput.terminalTargetRef E (orderWidth problem))).depth duration path.2 := by
  change ((PublicInput.initializeWork E (orderWidth problem)).depth duration path.1.1 +
    (PublicInput.allocateTerminal E (orderWidth problem)).depth duration path.1.2) + _ = _
  have noDepth :
      (PublicInput.allocateTerminal E (orderWidth problem)).depth duration path.1.2 = 0 :=
    MeasurementCells.allocateFramed_depth _ _ _ _ _ duration _
  rw [noDepth, add_zero, PublicInput.initializeWork_depth]
  rfl

/-- True three-event wire resets and original checked recovery give the unit-duration bound. -/
theorem exponentRepeatedRun_unitDepth_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.depth (fun _ => 1) path ≤
        2 + count * (samplingRoundUnitDepth E problem +
          attemptDepthLimit (kind := .quantum) (Canonical.Layout.curveSpec E)
            (recoveryModulusSpec problem nontrivial) (fun _ => 1)) + 1 := by
  rw [exponentRepeatedRun_duration]
  have later := sampledRecoveryTail_depth_le
    (samplingRound E fieldTail sameWidth fits odd problem points seed)
    (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _
    (fun _ => 1) (samplingRoundUnitDepth E problem)
    (samplingRound_unitDepth_le E fieldTail sameWidth fits odd problem points seed) path.2
  exact (Nat.add_le_add_left later 2).trans_eq (Nat.add_assoc _ _ _).symm

omit [Fact p.Prime] in
private theorem initial_resident (exponentWidth : Nat)
    (path : ((PublicInput.initializeWork E exponentWidth).seq
      (PublicInput.allocateTerminal E exponentWidth)).Path) :
    ((PublicInput.initializeWork E exponentWidth).seq
      (PublicInput.allocateTerminal E exponentWidth)).peakResidentSpace path =
        (PublicInput.terminal E exponentWidth).residentSpace := by
  have cells : (PublicInput.allocateTerminal E exponentWidth).peakResidentSpace path.2 =
      (PublicInput.terminal E exponentWidth).residentSpace :=
    (MeasurementCells.allocateFramed_peakResidentSpace _ _ _ _ _ _).trans
      (RuntimeCtx.residentSpace_disjointUnion _ _ _).symm
  have bound := (Circuit.input_residentSpace_le_peak
    (PublicInput.allocateTerminal E exponentWidth) path.2).trans_eq cells
  exact (Circuit.peakResidentSpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max (PublicInput.initialization_resident E exponentWidth path.1)
      cells).trans (SpacePool.max_eq_right bound))

omit [Fact p.Prime] in
private theorem initial_auxiliary (exponentWidth : Nat)
    (path : ((PublicInput.initializeWork E exponentWidth).seq
      (PublicInput.allocateTerminal E exponentWidth)).Path) :
    ((PublicInput.initializeWork E exponentWidth).seq
      (PublicInput.allocateTerminal E exponentWidth)).peakAuxiliarySpace path =
        (PublicInput.terminal E exponentWidth).auxiliarySpace := by
  have cells : (PublicInput.allocateTerminal E exponentWidth).peakAuxiliarySpace path.2 =
      (PublicInput.terminal E exponentWidth).auxiliarySpace :=
    (MeasurementCells.allocateFramed_peakAuxiliarySpace _ _ _ _ _ _).trans
      (RuntimeCtx.auxiliarySpace_disjointUnion _ _ _).symm
  have bound := (Circuit.input_auxiliarySpace_le_peak
    (PublicInput.allocateTerminal E exponentWidth) path.2).trans_eq cells
  exact (Circuit.peakAuxiliarySpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max (PublicInput.initialization_auxiliary E exponentWidth path.1)
      cells).trans (SpacePool.max_eq_right bound))

/-- The full resident allowance contains both public points, quantum storage and real scratch. -/
theorem exponentRepeatedRun_resident_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.peakResidentSpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [initial_resident]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_resident_le
      (samplingRound E fieldTail sameWidth fits odd problem points seed)
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _ path.2

/-- All auxiliary roles are charged once; only successive lexical peaks use a maximum. -/
theorem exponentRepeatedRun_auxiliary_le
    (path : (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.Path) :
    (exponentRepeatedRun E fieldTail sameWidth fits odd problem points seed
      nontrivial count).code.peakAuxiliarySpace path ≤
        recoveryTailScratchSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
          persistentCellSpace .quantum (Canonical.Layout.fieldWidth E) (orderWidth problem) +
            (PublicInput.terminal E (orderWidth problem)).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [initial_auxiliary]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_auxiliary_le
      (samplingRound E fieldTail sameWidth fits odd problem points seed)
      (samplingRound_isLocal E fieldTail sameWidth fits odd problem points seed) count
      (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial) _ _ _ path.2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
