/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Packing
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Resources

/-!
# Complete allocated recovery-tail resources

Seven real persistent allocations precede the original complete attempt loop.
One real optional-result allocation and its pack instruction follow the loop.
Every declared attempt contributes its own native events and serial durations;
all persistent and original caller storage remains live and is charged once.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- The same complete tail includes every actual attempt and its final option-pack event. -/
def recoveryTailEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (count : Nat) : ResourcePool model :=
  repeatedAttemptsEnvelope model curve modulus count +
    ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption scalarWidth)))]

/-- The final optional result and the loop's lexical scratch occur in successive scopes. -/
def recoveryTailScratchSpace (kind : ProblemKind) (width scalarWidth : Nat) : SpacePool kind :=
  SpacePool.max (attemptScratchSpace kind width scalarWidth)
    (SpacePool.ofShape (.option (.unsignedWord scalarWidth)))

variable (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))

/-- Actual initial retention leaves the complete loop's native event list unchanged. -/
theorem recoveryBatch_eventTrace
    (path : (recoveryBatch curve modulus samples base target).Path) :
    (recoveryBatch curve modulus samples base target).eventTrace path =
      (repeatedAttempts curve modulus samples base target).eventTrace path.2 := by
  change (retainPersistent ctx width scalarWidth).eventTrace path.1 ++ _ = _
  rw [retainPersistent_eventTrace, List.nil_append]

/-- The complete allocated loop obeys the same original repeated native allowance. -/
theorem recoveryBatch_pool_le
    (path : (recoveryBatch curve modulus samples base target).Path) :
    (recoveryBatch curve modulus samples base target).resourcePool path ≤
      repeatedAttemptsEnvelope model curve modulus count := by
  rw [Circuit.resourcePool, recoveryBatch_eventTrace]
  exact repeatedAttempts_pool_le curve modulus samples base target path.2

/-- Real allocation adds no native duration to the original serial attempt loop. -/
theorem recoveryBatch_depth_le (duration : Resource.Event model → Nat)
    (path : (recoveryBatch curve modulus samples base target).Path) :
    (recoveryBatch curve modulus samples base target).depth duration path ≤
      count * attemptDepthLimit curve modulus duration := by
  change (retainPersistent ctx width scalarWidth).depth duration path.1 + _ ≤ _
  rw [retainPersistent_depth, zero_add]
  exact repeatedAttempts_depth_le curve modulus samples base target duration path.2

/-- Resident allocation and all actual iterations retain one persistent context beside scratch. -/
theorem recoveryBatch_resident_le
    (path : (recoveryBatch curve modulus samples base target).Path) :
    (recoveryBatch curve modulus samples base target).peakResidentSpace path ≤
      attemptScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [retainPersistent_resident]
    exact fun _ => Nat.le_add_left _ _
  · exact repeatedAttempts_resident_le curve modulus samples base target path.2

/-- Auxiliary allocation and all actual iterations retain the same original caller roles. -/
theorem recoveryBatch_auxiliary_le
    (path : (recoveryBatch curve modulus samples base target).Path) :
    (recoveryBatch curve modulus samples base target).peakAuxiliarySpace path ≤
      attemptScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · rw [retainPersistent_auxiliary]
    exact fun _ => Nat.le_add_left _ _
  · exact repeatedAttempts_auxiliary_le curve modulus samples base target path.2

/-- Final packing follows the full actual loop on the same complete recorded path. -/
theorem recoveryTail_pool_le
    (path : (recoveryTail curve modulus samples base target).Path) :
    (recoveryTail curve modulus samples base target).resourcePool path ≤
      recoveryTailEnvelope model curve modulus count := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (recoveryBatch_pool_le curve modulus samples base target path.1)
    (packBatchResult_resourcePool ctx width scalarWidth path.2).le

/-- The same complete tail keeps all attempt durations and the final pack dependency. -/
theorem recoveryTail_depth_le (duration : Resource.Event model → Nat)
    (path : (recoveryTail curve modulus samples base target).Path) :
    (recoveryTail curve modulus samples base target).depth duration path ≤
      count * attemptDepthLimit curve modulus duration +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packOption scalarWidth)))) :=
  Nat.add_le_add (recoveryBatch_depth_le curve modulus samples base target duration path.1)
    (packBatchResult_depth ctx width scalarWidth duration path.2).le

/-- The resident bound includes all eight retained cells and every original caller entry. -/
theorem recoveryTail_resident_le
    (path : (recoveryTail curve modulus samples base target).Path) :
    (recoveryTail curve modulus samples base target).peakResidentSpace path ≤
      recoveryTailScratchSpace model.kind width scalarWidth +
        persistentCellSpace model.kind width scalarWidth +
        ctx.residentSpace := by
  have bounded : (recoveryTail curve modulus samples base target).peakResidentSpace path ≤
      recoveryTailScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · exact (recoveryBatch_resident_le curve modulus samples base target path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_resident ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_residentSpace, add_assoc] using bounded

/-- The complete auxiliary bound preserves caller roles and charges actual retained results. -/
theorem recoveryTail_auxiliary_le
    (path : (recoveryTail curve modulus samples base target).Path) :
    (recoveryTail curve modulus samples base target).peakAuxiliarySpace path ≤
      recoveryTailScratchSpace model.kind width scalarWidth +
        persistentCellSpace model.kind width scalarWidth +
        ctx.auxiliarySpace := by
  have bounded : (recoveryTail curve modulus samples base target).peakAuxiliarySpace path ≤
      recoveryTailScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · exact (recoveryBatch_auxiliary_le curve modulus samples base target path.1).trans
        (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_auxiliary ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_auxiliarySpace, add_assoc] using bounded

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
