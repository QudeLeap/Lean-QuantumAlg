/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Sampling.Resources

/-!
# Allocated interleaved sampling-tail resources

The seven persistent cells are retained once, all actual sampling and checking
rounds execute, and one final optional cell is retained and packed. Resident
and auxiliary bounds include the complete original context and the maximum
of reused checked scratch and final result storage, independently of count.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

/-- The actual interleaved loop is followed by its one original final pack instruction. -/
def sampledRecoveryEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (sampleBudget : ResourcePool model)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) (count : Nat) :
    ResourcePool model :=
  sampledAttemptsEnvelope model sampleBudget curve modulus count +
    ResourcePool.ofList [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.nominalEncoding (.packOption scalarWidth)))]

/-- Nearest scratch and the final option occur in successive actual scopes. -/
def recoveryTailScratchSpace (kind : ProblemKind) (width scalarWidth : Nat) : SpacePool kind :=
  SpacePool.max (attemptScratchSpace kind width scalarWidth)
    (SpacePool.ofShape (.option (.unsignedWord scalarWidth)))

variable (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))

/-- Actual allocation adds no event; the same loop path is followed by one final pack. -/
lemma sampledRecoveryTail_eventTrace
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base target).eventTrace
      path =
        (sampledAttempts sampleCode count curve modulus sample base target).eventTrace
          path.1.2 ++ [.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.nominalEncoding (.packOption scalarWidth)))] := by
  change ((retainPersistent ctx width scalarWidth).eventTrace path.1.1 ++ _) ++
    (packBatchResult ctx width scalarWidth).eventTrace path.2 = _
  rw [retainPersistent_eventTrace, List.nil_append, packBatchResult_eventTrace]

/-- The exact loop duration is followed by the one actual final packing dependency. -/
lemma sampledRecoveryTail_duration (duration : Resource.Event model → Nat)
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base target).depth
      duration path =
        (sampledAttempts sampleCode count curve modulus sample base target).depth
          duration path.1.2 +
            duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
              (.nominalEncoding (.packOption scalarWidth)))) := by
  change ((retainPersistent ctx width scalarWidth).depth duration path.1.1 + _) +
    (packBatchResult ctx width scalarWidth).depth duration path.2 = _
  rw [retainPersistent_depth, zero_add, packBatchResult_depth]
  rfl

/-- Every round's actual events and the final real pack remain in the complete native allowance. -/
lemma sampledRecoveryTail_pool_le (sampleBudget : ResourcePool model)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base target).resourcePool
      path ≤ sampledRecoveryEnvelope model sampleBudget curve modulus count := by
  rw [Circuit.resourcePool, sampledRecoveryTail_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (sampledAttempts_pool_le sampleCode curve modulus sample base target
    count sampleBudget sampleBound path.1.2) le_rfl

/-- Counting the actual budget includes all native classical instructions as well as sampling. -/
lemma sampledRecoveryTail_eventCount_le (sampleBudget : ResourcePool model)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    ((sampledRecoveryTail sampleCode count curve modulus sample base target).eventTrace
      path).length ≤
        count * (sampleBudget.card + (attemptEnvelope model curve modulus).card) + 1 := by
  have bounded := Multiset.card_le_card (sampledRecoveryTail_pool_le sampleCode count
    curve modulus sample base target sampleBudget sampleBound path)
  simpa only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card,
    sampledRecoveryEnvelope, sampledAttemptsEnvelope, ResourcePool.scale, Multiset.card_add,
    Multiset.card_nsmul, smul_eq_mul, List.length_singleton] using bounded

/-- Arbitrary durations sum across all actual rounds and the final pack, including count zero. -/
lemma sampledRecoveryTail_depth_le (duration : Resource.Event model → Nat)
    (sampleDepth : Nat) (sampleBound : ∀ path, sampleCode.depth duration path ≤ sampleDepth)
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base target).depth
      duration path ≤ count * (sampleDepth + attemptDepthLimit curve modulus duration) +
        duration (.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.nominalEncoding (.packOption scalarWidth)))) := by
  rw [sampledRecoveryTail_duration]
  exact Nat.add_le_add (sampledAttempts_depth_le sampleCode curve modulus sample base
    target count duration sampleDepth sampleBound path.1.2) le_rfl

/-- All original residents and all actual persistent destinations are charged once. -/
lemma sampledRecoveryTail_resident_le
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base
      target).peakResidentSpace
      path ≤ recoveryTailScratchSpace model.kind width scalarWidth +
        persistentCellSpace model.kind width scalarWidth + ctx.residentSpace := by
  have bounded :
      (sampledRecoveryTail sampleCode count curve modulus sample base
      target).peakResidentSpace
        path ≤ recoveryTailScratchSpace model.kind width scalarWidth +
          (persistentCtx ctx width scalarWidth).residentSpace := by
    refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakResidentSpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
      · rw [retainPersistent_resident]
        exact fun _ => Nat.le_add_left _ _
      · exact (sampledAttempts_resident_le sampleCode curve modulus sample base target
          count path.1.2).trans (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_resident ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_residentSpace, add_assoc] using bounded

/-- The reused auxiliary allowance retains every original role and does not grow with count. -/
lemma sampledRecoveryTail_auxiliary_le
    (path :
      (sampledRecoveryTail sampleCode count curve modulus sample base target).Path) :
    (sampledRecoveryTail sampleCode count curve modulus sample base
      target).peakAuxiliarySpace
      path ≤ recoveryTailScratchSpace model.kind width scalarWidth +
        persistentCellSpace model.kind width scalarWidth + ctx.auxiliarySpace := by
  have bounded :
      (sampledRecoveryTail sampleCode count curve modulus sample base
      target).peakAuxiliarySpace
        path ≤ recoveryTailScratchSpace model.kind width scalarWidth +
          (persistentCtx ctx width scalarWidth).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
    · refine (Circuit.peakAuxiliarySpace_seq _ _ path.1).le.trans (SpacePool.max_le ?_ ?_)
      · rw [retainPersistent_auxiliary]
        exact fun _ => Nat.le_add_left _ _
      · exact (sampledAttempts_auxiliary_le sampleCode curve modulus sample base target
          count path.1.2).trans (add_le_add (SpacePool.le_max_left _ _) le_rfl)
    · exact (packBatchResult_auxiliary ctx width scalarWidth path.2).le.trans
        (add_le_add (SpacePool.le_max_right _ _) le_rfl)
  simpa only [persistentCtx_auxiliarySpace, add_assoc] using bounded

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
