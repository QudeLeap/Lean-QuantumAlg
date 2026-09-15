/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Program.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space

/-!
# Actual candidate modular-power resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

open Execution
open ClassicalAlgorithms.Modular
open ClassicalRoutines.Modular.NativePower

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width exponentWidth : Nat}

/-- Independent shared native-power allowance followed by the original equality test. -/
def candidatePowerEventEnvelope (kind : ProblemKind) (width exponentWidth : Nat) :
    ResourcePool kind :=
  eventEnvelope kind width exponentWidth +
    ResourcePool.singleton (.classicalOperation (.wordBinary .equal width))

/-- The original target equality follows precisely the actual shared power path. -/
theorem candidatePowerInto_events (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).eventTrace path =
      (into spec refs.generator refs.exponent refs.power).eventTrace path.1 ++
        [.classicalOperation (.wordBinary .equal width)] := rfl

/-- The actual native pool contains the selected power instructions and one actual equality. -/
theorem candidatePowerInto_resourcePool (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).resourcePool path =
      (into spec refs.generator refs.exponent refs.power).resourcePool path.1 +
        ResourcePool.singleton (.classicalOperation (.wordBinary .equal width)) := by
  change ResourcePool.ofList (_ ++ [_]) = _
  rw [ResourcePool.ofList_append]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  rfl

/-- Actual native multiplicities fit the independent complete powering and comparison budget. -/
theorem candidatePowerInto_pool_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).resourcePool path ≤
      candidatePowerEventEnvelope kind width exponentWidth := by
  rw [candidatePowerInto_resourcePool]
  exact add_le_add (nativePower_into_pool_le spec refs.generator refs.exponent refs.power path.1)
    le_rfl

/-- The actual dependency depth counts every initialization, selected multiply and final test. -/
theorem candidatePowerInto_depth_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (duration : Resource.Event kind → Nat)
    (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).depth duration path ≤
      depthBound width exponentWidth duration +
        duration (.classicalOperation (.wordBinary .equal width)) :=
  Nat.add_le_add_right
    (nativePower_into_depth_le spec refs.generator refs.exponent refs.power duration path.1) _

/-- Unit native durations meet the original source width's independent complete step bound. -/
theorem candidatePowerInto_unitDepth_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).depth (fun _ => 1) path ≤
      2 * width + 6 + 6 * exponentWidth := by
  have actual := nativePower_into_unitDepth_le spec refs.generator refs.exponent refs.power path.1
  change (into spec refs.generator refs.exponent refs.power).depth (fun _ => 1) path.1 + 1 ≤ _
  omega

/-- Actual power scopes, selected arithmetic and equality restore all borrowed correlations. -/
theorem candidatePowerInto_borrowedRestored (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidatePowerInto spec refs).BorrowedRestored Reference state
      ((candidatePowerInto spec refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (nativePower_into_borrowedRestored spec refs.generator refs.exponent refs.power Reference state)
    (Circuit.borrowedRestored_classical _ _)

/-- The actual final equality retains the original supplied resident context. -/
theorem equality_resident_le (refs : Refs ctx width exponentWidth)
    (path : (Circuit.classical (equalityOp refs)).Path) :
    (Circuit.classical (equalityOp refs)).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

/-- The actual final equality retains the original supplied auxiliary roles. -/
theorem equality_auxiliary_le (refs : Refs ctx width exponentWidth)
    (path : (Circuit.classical (equalityOp refs)).Path) :
    (Circuit.classical (equalityOp refs)).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

/-- Resident peak counts all original caller storage and the real lexical power scratch. -/
theorem candidatePowerInto_resident_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).peakResidentSpace path ≤
      ctx.residentSpace + powerSpace kind width := by
  refine (Circuit.peakResidentSpace_seq (powerInto spec refs)
    (.classical (equalityOp refs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact nativePower_into_resident_le spec refs.generator refs.exponent refs.power path.1
  · exact (equality_resident_le refs path.2).trans (le_add_of_nonneg_right zero_le)

/-- Every actual temporary power bit remains charged as auxiliary at its simultaneous peak. -/
theorem candidatePowerInto_auxiliary_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + powerSpace kind width := by
  refine (Circuit.peakAuxiliarySpace_seq (powerInto spec refs)
    (.classical (equalityOp refs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact nativePower_into_auxiliary_le spec refs.generator refs.exponent refs.power path.1
  · exact (equality_auxiliary_le refs path.2).trans (le_add_of_nonneg_right zero_le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine
