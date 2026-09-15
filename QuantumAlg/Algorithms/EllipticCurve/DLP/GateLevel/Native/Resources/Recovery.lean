/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.TailResources

/-!
# Complete actual opaque ECDLP recovery resources

The one original bank and finite readout bank are allocated once. Every
actual round, including the first, resets that bank, samples and immediately
checks the stored candidate. Seven persistent cells survive all rounds;
one final optional result is retained and packed. Independent coordinate
budgets retain every caller entry, the bank and all surviving results.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- One real initialization and the independent full sampling-and-checking envelope. -/
def recoveryEnvelope (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (count : Nat) :
    ResourcePool .quantum :=
  ResourcePool.singleton (preparation I).event +
    sampledRecoveryEnvelope .quantum (reusedSampleEnvelope I B)
      (Layout.curveSpec E) (recoveryModulus I) count

/-- Actual correction choices save one reset alternative per original wire in each round. -/
def recoveryEventLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (count : Nat) : Nat :=
  2 + count * (3 * Layout.totalQubits I + (sampleEnvelope I B).card +
    (attemptEnvelope .quantum (Layout.curveSpec E) (recoveryModulus I)).card)

/-- The original member critical path, paid reset and complete actual recovery dependencies. -/
def recoveryDepthLimit (I : ECDLPInstance E) (B : OrderExpansion (problem I).order)
    (count : Nat) : Nat :=
  2 + count * (reusedSampleDepthLimit I B +
    attemptDepthLimit (kind := .quantum) (Layout.curveSpec E) (recoveryModulus I) (fun _ => 1))

/-- Real recovery scratch, seven persistent cells and the complete original sampling bank. -/
def recoverySpace (I : ECDLPInstance E) : SpacePool .quantum :=
  recoveryTailScratchSpace .quantum (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I)) +
    persistentCellSpace .quantum (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I)) +
      samplingSpace I

private theorem sampled_attempt_count {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (limit : Nat) (bound : ∀ path, (code.eventTrace path).length ≤ limit)
    (path : (sampledAttempt code supported curve modulus sample base target).Path) :
    ((sampledAttempt code supported curve modulus sample base target).eventTrace path).length ≤
      limit + (attemptEnvelope kind curve modulus).card := by
  rw [sampledAttempt_eventTrace, List.length_append]
  exact Nat.add_le_add (bound _) (Multiset.card_le_card
    (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2))

private theorem sampled_tail_count {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {width scalarWidth : Nat} (code : Circuit ctx ctx) (supported : code.IsLocal)
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (ClassicalRoutines.EllipticCurve.PointShape width))
    (count limit : Nat) (bound : ∀ path, (code.eventTrace path).length ≤ limit)
    (path : (sampledRecoveryTail code supported count curve modulus sample base target).Path) :
    ((sampledRecoveryTail code supported count curve modulus sample base target).eventTrace
      path).length ≤ count * (limit + (attemptEnvelope kind curve modulus).card) + 1 := by
  rw [sampledRecoveryTail_eventTrace, List.length_append, List.length_singleton]
  exact Nat.add_le_add_right (Circuit.forRange_eventCount_le count _ _
    (fun _ => sampled_attempt_count code supported curve modulus sample base target limit bound)
    path.1.2) 1

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)
    (B : OrderExpansion (problem I).order) (A : Access I) (count : Nat)
    (basePoint targetPoint : CInputRef base
      (ClassicalRoutines.EllipticCurve.PointShape (Layout.fieldWidth E)))

attribute [local irreducible] underPersistent

/-- The same complete actual run fits the original literal and checked-recovery event budgets. -/
theorem nativeECDLP_recovery_pool_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    (recoveryRun base noQuantum I B A count basePoint targetPoint).code.resourcePool path ≤
      recoveryEnvelope I B count := by
  change ResourcePool.ofList ((allocate base noQuantum I).eventTrace path.1 ++
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)).eventTrace
        path.2) ≤ _
  rw [ResourcePool.ofList_append, nativeECDLP_allocate_events]
  exact add_le_add le_rfl (sampledRecoveryTail_pool_le _ _ _ _ _ _ _ _
    (reusedSampleEnvelope I B) (nativeECDLP_reusedSample_pool_le base noQuantum I B A) path.2)

/-- All count rounds reset the original bank; only selected corrections contribute to this bound. -/
theorem nativeECDLP_recovery_eventCount_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    ((recoveryRun base noQuantum I B A count basePoint targetPoint).code.eventTrace path).length ≤
      recoveryEventLimit I B count := by
  change ((allocate base noQuantum I).eventTrace path.1 ++
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)).eventTrace
        path.2).length ≤ _
  rw [List.length_append, nativeECDLP_allocate_events, List.length_singleton]
  have bounded := sampled_tail_count (reusedSample base noQuantum I B A)
    (nativeECDLP_reusedSample_isLocal base noQuantum I B A)
    (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
    (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint) count
    (3 * Layout.totalQubits I + (sampleEnvelope I B).card)
    (nativeECDLP_reusedSample_eventCount_le base noQuantum I B A) path.2
  unfold recoveryEventLimit
  omega

/-- The actual unit depth retains the member's parallel structure and all serial recovery stages. -/
theorem nativeECDLP_recovery_depth_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    (recoveryRun base noQuantum I B A count basePoint targetPoint).code.depth (fun _ => 1) path ≤
      recoveryDepthLimit I B count := by
  change (allocate base noQuantum I).depth (fun _ => 1) path.1 +
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)).depth
        (fun _ => 1) path.2 ≤ _
  rw [nativeECDLP_allocate_depth]
  have bounded := sampledRecoveryTail_depth_le (reusedSample base noQuantum I B A)
    (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
    (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
    (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint)
    (fun _ => 1) (reusedSampleDepthLimit I B)
    (nativeECDLP_reusedSample_depth_le base noQuantum I B A) path.2
  unfold recoveryDepthLimit
  omega

/-- The bank, all readouts, persistent cells, scratch and final optional result remain charged. -/
theorem nativeECDLP_recovery_resident_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    (recoveryRun base noQuantum I B A count basePoint targetPoint).code.peakResidentSpace path ≤
      recoverySpace I + base.residentSpace := by
  change ((allocate base noQuantum I).seq
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint)
      (liftInput base noQuantum I targetPoint))).peakResidentSpace path ≤ _
  refine (Circuit.peakResidentSpace_seq (allocate base noQuantum I)
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint)
      (liftInput base noQuantum I targetPoint)) path).le.trans
        (SpacePool.max_le ?_ ?_)
  · refine (nativeECDLP_allocate_resident base noQuantum I path.1).trans ?_
    rw [nativeECDLP_context_residentSpace]
    intro axis
    change samplingSpace I axis + base.residentSpace axis ≤ _ + _ + samplingSpace I axis + _
    omega
  · have bounded := sampledRecoveryTail_resident_le (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint) path.2
    simpa only [nativeECDLP_context_residentSpace,
      recoverySpace, add_assoc] using bounded

/-- Auxiliary roles include the same new storage and the caller's original auxiliary footprint. -/
theorem nativeECDLP_recovery_auxiliary_le
    (path : (recoveryRun base noQuantum I B A count basePoint targetPoint).code.Path) :
    (recoveryRun base noQuantum I B A count basePoint targetPoint).code.peakAuxiliarySpace path ≤
      recoverySpace I + base.auxiliarySpace := by
  change ((allocate base noQuantum I).seq
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint)
      (liftInput base noQuantum I targetPoint))).peakAuxiliarySpace path ≤ _
  refine (Circuit.peakAuxiliarySpace_seq (allocate base noQuantum I)
    (sampledRecoveryTail (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint)
      (liftInput base noQuantum I targetPoint)) path).le.trans
        (SpacePool.max_le ?_ ?_)
  · refine (nativeECDLP_allocate_auxiliary base noQuantum I path.1).trans ?_
    rw [nativeECDLP_context_auxiliarySpace]
    intro axis
    change samplingSpace I axis + base.auxiliarySpace axis ≤ _ + _ + samplingSpace I axis + _
    omega
  · have bounded := sampledRecoveryTail_auxiliary_le (reusedSample base noQuantum I B A)
      (nativeECDLP_reusedSample_isLocal base noQuantum I B A) count
      (Layout.curveSpec E) (recoveryModulus I) (sampleInput base noQuantum I)
      (liftInput base noQuantum I basePoint) (liftInput base noQuantum I targetPoint) path.2
    simpa only [nativeECDLP_context_auxiliarySpace,
      recoverySpace, add_assoc] using bounded

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
