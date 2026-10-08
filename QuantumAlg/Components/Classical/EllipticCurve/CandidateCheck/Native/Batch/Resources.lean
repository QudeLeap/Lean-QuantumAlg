/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Attempt.Resources
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Resources

/-!
# Actual repeated recovery resources

Every declared sample executes the same original six-stage attempt. Native
events and serial durations therefore add across all declared iterations.
The seven real persistent cells remain allocated throughout the loop, while
each attempt releases its lexical scratch before the next attempt. The space
allowance retains the full caller context without multiplying it by the count.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth count : Nat}

/-- All declared iterations contribute their original independent native allowance. -/
def repeatedAttemptsEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (count : Nat) : ResourcePool model :=
  ResourcePool.scale count (attemptEnvelope model curve modulus)

variable (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))

/-- The actual loop pool keeps the original full allowance for every declared attempt. -/
theorem repeatedAttempts_pool_le
    (path : (repeatedAttempts curve modulus samples base target).Path) :
    (repeatedAttempts curve modulus samples base target).resourcePool path ≤
      repeatedAttemptsEnvelope model curve modulus count := by
  exact Circuit.forRange_pool_le count
    (fun index => persistentAttempt curve modulus (samples index) base target)
    (attemptEnvelope model curve modulus)
    (fun _ iteration => attemptInto_pool_le curve modulus _ _ _ _ _ _ _ _ _ _ iteration) path

/-- Counting the same native pool includes every actual event on this path. -/
theorem repeatedAttempts_eventCount_le
    (path : (repeatedAttempts curve modulus samples base target).Path) :
    ((repeatedAttempts curve modulus samples base target).eventTrace path).length ≤
      count * (attemptEnvelope model curve modulus).card := by
  have bounded := Multiset.card_le_card
    (repeatedAttempts_pool_le curve modulus samples base target path)
  simpa only [Circuit.resourcePool, ResourcePool.ofList, Multiset.coe_card,
    repeatedAttemptsEnvelope, ResourcePool.scale, Multiset.card_nsmul, smul_eq_mul] using bounded

/-- Arbitrary event durations retain the serial order of every actual attempt. -/
theorem repeatedAttempts_depth_le (duration : Resource.Event model → Nat)
    (path : (repeatedAttempts curve modulus samples base target).Path) :
    (repeatedAttempts curve modulus samples base target).depth duration path ≤
      count * attemptDepthLimit curve modulus duration := by
  have bounded := Circuit.forRange_depth_le_sum count
    (fun index => persistentAttempt curve modulus (samples index) base target) duration
    (fun _ => attemptDepthLimit curve modulus duration)
    (fun _ iteration => attemptInto_depth_le curve modulus _ _ _ _ _ _ _ _ _ _ duration iteration)
    path
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at bounded
  exact bounded

/-- All persistent cells and original caller residents are charged once beside reused scratch. -/
theorem repeatedAttempts_resident_le
    (path : (repeatedAttempts curve modulus samples base target).Path) :
    (repeatedAttempts curve modulus samples base target).peakResidentSpace path ≤
      attemptScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).residentSpace := by
  exact Circuit.forRange_resident_le count
    (fun index => persistentAttempt curve modulus (samples index) base target) _
    (fun _ => Nat.le_add_left _ _)
    (fun _ iteration => attemptInto_resident_le curve modulus _ _ _ _ _ _ _ _ _ _ iteration) path

/-- Original auxiliary roles and the same persistent destinations remain live across the loop. -/
theorem repeatedAttempts_auxiliary_le
    (path : (repeatedAttempts curve modulus samples base target).Path) :
    (repeatedAttempts curve modulus samples base target).peakAuxiliarySpace path ≤
      attemptScratchSpace model.kind width scalarWidth +
        (persistentCtx ctx width scalarWidth).auxiliarySpace := by
  exact Circuit.forRange_auxiliary_le count
    (fun index => persistentAttempt curve modulus (samples index) base target) _
    (fun _ => Nat.le_add_left _ _)
    (fun _ iteration => attemptInto_auxiliary_le curve modulus _ _ _ _ _ _ _ _ _ _ iteration) path

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
