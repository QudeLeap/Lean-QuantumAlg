/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Resources

/-!
# Allocated interleaved sampling-tail resources

The seven persistent cells are retained once, all actual sampling and checking
rounds execute, and one final optional cell is retained and packed. Resident
and auxiliary bounds include the complete original context and the maximum
of reused checked scratch and final result storage, independently of count.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The actual interleaved loop is followed by its one original final pack instruction. -/
def sampledRecoveryEnvelope (kind : ProblemKind) (sampleBudget : ResourcePool kind)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) (count : Nat) :
    ResourcePool kind :=
  sampledAttemptsEnvelope kind sampleBudget curve modulus count +
    ResourcePool.ofList [.classicalOperation (.nominalEncoding (.packOption scalarWidth))]

variable (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))

/-- Actual allocation adds no event; the same loop path is followed by one final pack. -/
theorem sampledRecoveryTail_eventTrace
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base target).eventTrace
      path =
        (sampledAttempts sampleCode supported count curve modulus sample base target).eventTrace
          path.1.2 ++ [.classicalOperation (.nominalEncoding (.packOption scalarWidth))] := by
  change ((retainPersistent ctx width scalarWidth).eventTrace path.1.1 ++ _) ++
    (packBatchResult ctx width scalarWidth).eventTrace path.2 = _
  rw [retainPersistent_eventTrace, List.nil_append, packBatchResult_eventTrace]

/-- The exact loop duration is followed by the one actual final packing dependency. -/
theorem sampledRecoveryTail_duration (duration : Resource.Event kind → Nat)
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base target).depth
      duration path =
        (sampledAttempts sampleCode supported count curve modulus sample base target).depth
          duration path.1.2 +
            duration (.classicalOperation (.nominalEncoding (.packOption scalarWidth))) := by
  change ((retainPersistent ctx width scalarWidth).depth duration path.1.1 + _) +
    (packBatchResult ctx width scalarWidth).depth duration path.2 = _
  rw [retainPersistent_depth, zero_add, packBatchResult_depth]
  rfl

/-- Every round's actual events and the final real pack remain in the complete native allowance. -/
theorem sampledRecoveryTail_pool_le (sampleBudget : ResourcePool kind)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base target).resourcePool
      path ≤ sampledRecoveryEnvelope kind sampleBudget curve modulus count := by
  rw [Circuit.resourcePool, sampledRecoveryTail_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (sampledAttempts_pool_le sampleCode supported curve modulus sample base target
    count sampleBudget sampleBound path.1.2) le_rfl

/-- Counting the actual budget includes all native classical instructions as well as sampling. -/
theorem sampledRecoveryTail_eventCount_le (sampleBudget : ResourcePool kind)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    ((sampledRecoveryTail sampleCode supported count curve modulus sample base target).eventTrace
      path).length ≤
        count * (sampleBudget.card + (attemptEnvelope kind curve modulus).card) + 1 := by
  have bounded := Multiset.card_le_card (sampledRecoveryTail_pool_le sampleCode supported count
    curve modulus sample base target sampleBudget sampleBound path)
  simpa only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card,
    sampledRecoveryEnvelope, sampledAttemptsEnvelope, ResourcePool.scale, Multiset.card_add,
    Multiset.card_nsmul, smul_eq_mul, List.length_singleton] using bounded

/-- Arbitrary durations sum across all actual rounds and the final pack, including count zero. -/
theorem sampledRecoveryTail_depth_le (duration : Resource.Event kind → Nat)
    (sampleDepth : Nat) (sampleBound : ∀ path, sampleCode.depth duration path ≤ sampleDepth)
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base target).depth
      duration path ≤ count * (sampleDepth + attemptDepthLimit curve modulus duration) +
        duration (.classicalOperation (.nominalEncoding (.packOption scalarWidth))) := by
  rw [sampledRecoveryTail_duration]
  exact Nat.add_le_add (sampledAttempts_depth_le sampleCode supported curve modulus sample base
    target count duration sampleDepth sampleBound path.1.2) le_rfl

/-- All original residents and all actual persistent destinations are charged once. -/
theorem sampledRecoveryTail_resident_le
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base
      target).peakResidentSpace
      path ≤ recoveryTailScratchSpace kind width scalarWidth +
        persistentCellSpace kind width scalarWidth + ctx.residentSpace := by
  have bounded :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base
      target).peakResidentSpace
        path ≤ recoveryTailScratchSpace kind width scalarWidth +
          (persistentCtx ctx width scalarWidth).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
      · rw [retainPersistent_resident]
        exact fun _ => Nat.le_add_left _ _
      · exact (sampledAttempts_resident_le sampleCode supported curve modulus sample base target
          count path.1.2).trans (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_resident ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_residentSpace, add_assoc] using bounded

/-- The reused auxiliary allowance retains every original role and does not grow with count. -/
theorem sampledRecoveryTail_auxiliary_le
    (path :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode supported count curve modulus sample base
      target).peakAuxiliarySpace
      path ≤ recoveryTailScratchSpace kind width scalarWidth +
        persistentCellSpace kind width scalarWidth + ctx.auxiliarySpace := by
  have bounded :
      (sampledRecoveryTail sampleCode supported count curve modulus sample base
      target).peakAuxiliarySpace
        path ≤ recoveryTailScratchSpace kind width scalarWidth +
          (persistentCtx ctx width scalarWidth).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
      · rw [retainPersistent_auxiliary]
        exact fun _ => Nat.le_add_left _ _
      · exact (sampledAttempts_auxiliary_le sampleCode supported curve modulus sample base target
          count path.1.2).trans (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_auxiliary ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_auxiliarySpace, add_assoc] using bounded

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
