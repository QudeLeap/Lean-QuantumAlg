/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Resources
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.TailResources

/-!
# Actual interleaved sampling and checked-recovery resources

Every real sampling path is followed by the original complete checked attempt.
All declared rounds execute. The same seven persistent destinations and the
same local quantum workspace remain live throughout the loop. The bounds for
a supplied sampler are statements about its actual code; they add no input,
correctness, cleanliness, or success premise to execution.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

private theorem sampled_trace {source outer : RuntimeCtx kind}
    (code : Circuit source source) (extended later : Circuit outer outer)
    (paths : code.Path ≃ extended.Path) (same : PathResources code extended paths)
    (path : (extended.seq later).Path) :
    (extended.seq later).eventTrace path =
      code.eventTrace (paths.symm path.1) ++ later.eventTrace path.2 := by
  change extended.eventTrace path.1 ++ _ = _
  congr 1
  simpa only [Equiv.apply_symm_apply] using same.1 (paths.symm path.1)

private theorem sampled_duration {source outer : RuntimeCtx kind}
    (code : Circuit source source) (extended later : Circuit outer outer)
    (paths : code.Path ≃ extended.Path) (same : PathResources code extended paths)
    (duration : Resource.Event kind → Nat) (path : (extended.seq later).Path) :
    (extended.seq later).depth duration path =
      code.depth duration (paths.symm path.1) + later.depth duration path.2 := by
  change extended.depth duration path.1 + _ = _
  congr 1
  simpa only [Equiv.apply_symm_apply] using same.2 duration (paths.symm path.1)

/-- All rounds contribute their native sampling and checked-attempt allowances. -/
def sampledAttemptsEnvelope (kind : ProblemKind) (sampleBudget : ResourcePool kind)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth) (count : Nat) :
    ResourcePool kind :=
  ResourcePool.scale count (sampleBudget + attemptEnvelope kind curve modulus)

variable (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))

/-- The same actual path contains the original sample events followed by checked recovery. -/
theorem sampledAttempt_eventTrace
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).eventTrace path =
      sampleCode.eventTrace
        ((underPersistentPathEquiv sampleCode supported width scalarWidth).symm path.1) ++
          (persistentAttempt curve modulus sample base target).eventTrace path.2 :=
  sampled_trace sampleCode _ _ _
    (underPersistent_pathResources sampleCode supported width scalarWidth) path

/-- Sampling and checking preserve their exact actual dependency durations in sequence. -/
theorem sampledAttempt_duration (duration : Resource.Event kind → Nat)
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).depth duration path =
      sampleCode.depth duration
        ((underPersistentPathEquiv sampleCode supported width scalarWidth).symm path.1) +
          (persistentAttempt curve modulus sample base target).depth duration path.2 :=
  sampled_duration sampleCode _ _ _
    (underPersistent_pathResources sampleCode supported width scalarWidth) duration path

/-- A round includes the actual sampler and every original native checking instruction. -/
theorem sampledAttempt_pool_le (sampleBudget : ResourcePool kind)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).resourcePool path ≤
      sampleBudget + attemptEnvelope kind curve modulus := by
  rw [Circuit.resourcePool, sampledAttempt_eventTrace, ResourcePool.ofList_append]
  exact add_le_add (sampleBound _) (attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2)

/-- Arbitrary durations retain the serial sampler and original checked-attempt allowance. -/
theorem sampledAttempt_depth_le (duration : Resource.Event kind → Nat) (sampleDepth : Nat)
    (sampleBound : ∀ path, sampleCode.depth duration path ≤ sampleDepth)
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).depth duration path ≤
      sampleDepth + attemptDepthLimit curve modulus duration := by
  rw [sampledAttempt_duration]
  exact Nat.add_le_add (sampleBound _)
    (attemptInto_depth_le curve modulus _ _ _ _ _ _ _ _ _ _ duration path.2)

/-- Local sampling adds no workspace beside the persistent cells and checked lexical scratch. -/
theorem sampledAttempt_resident_le
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).peakResidentSpace path ≤
      attemptScratchSpace kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  refine (Circuit.peakResidentSpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact ((underPersistent_space sampleCode supported width scalarWidth).1 path.1).le.trans
      (fun _ => Nat.le_add_left _ _)
  · exact attemptInto_resident_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2

/-- The same original auxiliary roles remain live while checked scratch is reused. -/
theorem sampledAttempt_auxiliary_le
    (path : (sampledAttempt sampleCode supported curve modulus sample base target).Path) :
    (sampledAttempt sampleCode supported curve modulus sample base target).peakAuxiliarySpace path ≤
      attemptScratchSpace kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq _ _ path).le.trans (SpacePool.max_le ?_ ?_)
  · exact ((underPersistent_space sampleCode supported width scalarWidth).2 path.1).le.trans
      (fun _ => Nat.le_add_left _ _)
  · exact attemptInto_auxiliary_le curve modulus _ _ _ _ _ _ _ _ _ _ path.2

/-- The actual finite loop charges sampling and original checked recovery for every round. -/
theorem sampledAttempts_pool_le (count : Nat) (sampleBudget : ResourcePool kind)
    (sampleBound : ∀ path, sampleCode.resourcePool path ≤ sampleBudget)
    (path : (sampledAttempts sampleCode supported count curve modulus sample base target).Path) :
    (sampledAttempts sampleCode supported count curve modulus sample base target).resourcePool
      path ≤
      sampledAttemptsEnvelope kind sampleBudget curve modulus count := by
  exact Circuit.forRange_pool_le count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target) _
    (fun _ iteration => sampledAttempt_pool_le sampleCode supported curve modulus sample base target
      sampleBudget sampleBound iteration) path

/-- Arbitrary duration allowances add across the actual declared sampling rounds. -/
theorem sampledAttempts_depth_le (count : Nat) (duration : Resource.Event kind → Nat)
    (sampleDepth : Nat) (sampleBound : ∀ path, sampleCode.depth duration path ≤ sampleDepth)
    (path : (sampledAttempts sampleCode supported count curve modulus sample base target).Path) :
    (sampledAttempts sampleCode supported count curve modulus sample base target).depth duration
      path ≤
      count * (sampleDepth + attemptDepthLimit curve modulus duration) := by
  have bounded := Circuit.forRange_depth_le_sum count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target) duration
    (fun _ => sampleDepth + attemptDepthLimit curve modulus duration)
    (fun _ iteration => sampledAttempt_depth_le sampleCode supported curve modulus sample base
      target
      duration sampleDepth sampleBound iteration) path
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at bounded
  exact bounded

/-- Resident storage is reused; its allowance is independent of the number of rounds. -/
theorem sampledAttempts_resident_le (count : Nat)
    (path : (sampledAttempts sampleCode supported count curve modulus sample base target).Path) :
    (sampledAttempts sampleCode supported count curve modulus sample base target).peakResidentSpace
      path ≤ attemptScratchSpace kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  exact Circuit.forRange_resident_le count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target) _
    (fun _ => Nat.le_add_left _ _)
    (fun _ iteration => sampledAttempt_resident_le sampleCode supported curve modulus sample base
      target iteration) path

/-- Auxiliary roles and lexical scratch have the same count-independent allowance. -/
theorem sampledAttempts_auxiliary_le (count : Nat)
    (path : (sampledAttempts sampleCode supported count curve modulus sample base target).Path) :
    (sampledAttempts sampleCode supported count curve modulus sample base target).peakAuxiliarySpace
      path ≤ attemptScratchSpace kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  exact Circuit.forRange_auxiliary_le count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target) _
    (fun _ => Nat.le_add_left _ _)
    (fun _ iteration => sampledAttempt_auxiliary_le sampleCode supported curve modulus sample base
      target iteration) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
