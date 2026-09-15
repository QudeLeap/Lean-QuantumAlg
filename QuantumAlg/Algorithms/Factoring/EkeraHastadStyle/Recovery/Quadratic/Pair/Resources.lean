/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair
import all QuantumAlg.Components.Classical.FirstAccepted.Resources

/-!
# Literal native resources of both checks and left-priority selection

The independent allowance contains twelve unconditional native checking
instructions and four instructions for each possible selector copy branch.
Actual traces retain both stored decisions. The total-event and unit-duration
serial-depth upper bound is twenty; source candidate calculation and enclosing
constant initialization have their own separate actual budgets.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent literal instruction list for a complete single-candidate check. -/
def checkEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .lessThan width),
    .classicalOperation (.wordBinary .lessThan width), .classicalOperation (.bit .and),
    .classicalOperation (.wordBinary .remainder width),
    .classicalOperation (.wordBinary .equal width), .classicalOperation (.bit .and)]

/-- Independent native coordinate allowance for both checks and both selector executions. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (checkEvents kind width) +
    (ResourcePool.ofList (checkEvents kind width) +
      (FirstAccepted.nativeEnvelope kind width + FirstAccepted.nativeEnvelope kind width))

/-- Every real check emits its six native instructions, including candidate zero. -/
theorem nativeQuadratic_check_eventTrace (refs : Check.Refs ctx width)
    (path : (Check.code refs).Path) :
    (Check.code refs).eventTrace path = checkEvents kind width := rfl

/-- The complete actual trace contains two checks followed by the two real selector branches. -/
theorem nativeQuadratic_pair_eventTrace (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).eventTrace path = checkEvents kind width ++
      (checkEvents kind width ++
        ((FirstAccepted.circuit (selectedInputs refs.first) refs.selection).eventTrace path.2.2.1 ++
          (FirstAccepted.circuit (selectedInputs refs.second) refs.selection).eventTrace
            path.2.2.2)) := rfl

/-- Every actual native coordinate is bounded by the independent twenty-instruction allowance. -/
theorem nativeQuadratic_pair_pool_le (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).resourcePool path ≤ nativeEnvelope kind width := by
  rw [Circuit.resourcePool, nativeQuadratic_pair_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (FirstAccepted.firstAccepted_pool_le _ _ path.2.2.1)
      (FirstAccepted.firstAccepted_pool_le _ _ path.2.2.2)))

/-- The independent native allowance contains exactly twenty instructions at every word width. -/
theorem nativeQuadratic_pair_nativeEnvelope_card (kind : ProblemKind) (width : Nat) :
    (nativeEnvelope kind width).card = 20 := rfl

/-- Actual total instructions count each real taken copy arm, after twelve unconditional checks. -/
theorem nativeQuadratic_pair_eventCount (refs : Refs ctx width) (path : (code refs).Path) :
    ((code refs).resourcePool path).card =
      12 + (if path.2.2.1.2.1.toBool then 4 else 2) +
        (if path.2.2.2.2.1.toBool then 4 else 2) := by
  rw [Circuit.resourcePool, nativeQuadratic_pair_eventTrace,
    FirstAccepted.firstAccepted_eventTrace, FirstAccepted.firstAccepted_eventTrace]
  change (checkEvents kind width ++
    (checkEvents kind width ++
      ((FirstAccepted.decisionEvents kind ++
        (if path.2.2.1.2.1.toBool then FirstAccepted.copyEvents kind width else [])) ++
      (FirstAccepted.decisionEvents kind ++
        (if path.2.2.2.2.1.toBool then FirstAccepted.copyEvents kind width else []))))).length = _
  split_ifs <;> rfl

/-- Unit native durations retain exactly the same actual serial instruction count. -/
theorem nativeQuadratic_pair_unitDepth (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).depth (fun _ => 1) path =
      12 + (if path.2.2.1.2.1.toBool then 4 else 2) +
        (if path.2.2.2.2.1.toBool then 4 else 2) := by
  change 6 + (6 +
    ((FirstAccepted.circuit (selectedInputs refs.first) refs.selection).depth (fun _ => 1)
      path.2.2.1 +
    (FirstAccepted.circuit (selectedInputs refs.second) refs.selection).depth (fun _ => 1)
      path.2.2.2)) = _
  rw [FirstAccepted.firstAccepted_unit_depth, FirstAccepted.firstAccepted_unit_depth]
  omega

/-- Both actual total events and unit-duration depth satisfy the same explicit upper bound. -/
theorem nativeQuadratic_pair_total_le (refs : Refs ctx width) (path : (code refs).Path) :
    ((code refs).resourcePool path).card ≤ 20 ∧
      (code refs).depth (fun _ => 1) path ≤ 20 := by
  rw [nativeQuadratic_pair_eventCount, nativeQuadratic_pair_unitDepth]
  split_ifs <;> omega

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair
