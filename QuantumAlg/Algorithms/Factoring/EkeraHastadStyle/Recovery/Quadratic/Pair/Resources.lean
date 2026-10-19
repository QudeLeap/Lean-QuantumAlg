/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange.Resources

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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent literal instruction list for a complete single-candidate check. -/
def checkEvents (width : Nat) : List (Resource.Event model) :=
  ([.wordBinary .lessThan width, .wordBinary .lessThan width, .bit .and,
    .wordBinary .remainder width, .wordBinary .equal width, .bit .and] :
      List Resource.ClassicalOpLabel).map
    (fun label => .classicalOperation (BitWord.selectedCoordinate (execution := model) label))

/-- Independent native coordinate allowance for both checks and both selector executions. -/
def nativeEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.ofList (checkEvents (model := model) width) +
    (ResourcePool.ofList (checkEvents (model := model) width) +
      (FirstAccepted.nativeEnvelope model width + FirstAccepted.nativeEnvelope model width))

/-- Every real check emits its six native instructions, including candidate zero. -/
lemma nativeQuadratic_check_eventTrace (refs : Check.Refs ctx width)
    (path : (Check.code (model := model) refs).Path) :
    (Check.code (model := model) refs).eventTrace path = checkEvents (model := model) width := by
  change (ClassicalRoutines.NumberTheory.FactorRange.code (model := model)
    (Check.rangeRefs refs)).eventTrace path.1 ++
      (Divisibility.code (model := model) refs.divisor).eventTrace path.2 = _
  rw [ClassicalRoutines.NumberTheory.FactorRange.code_eventTrace]
  change ClassicalRoutines.NumberTheory.FactorRange.events (model := model) width ++
    ((BitWord.instruction (execution := model)
      (Divisibility.remainderOp refs.divisor)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model)
        (Divisibility.equalityOp refs.divisor)).eventTrace path.2.2.1 ++
        (BitWord.instruction (execution := model)
          (Divisibility.combineOp refs.divisor)).eventTrace path.2.2.2)) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The complete actual trace contains two checks followed by the two real selector branches. -/
lemma nativeQuadratic_pair_eventTrace (refs : Refs ctx width) (path : (code (model := model)
  refs).Path) :
    (code (model := model) refs).eventTrace path = checkEvents (model := model) width ++
      (checkEvents (model := model) width ++
        ((FirstAccepted.circuit (model := model) (selectedInputs refs.first)
          refs.selection).eventTrace path.2.2.1 ++
          (FirstAccepted.circuit (model := model) (selectedInputs refs.second)
            refs.selection).eventTrace
            path.2.2.2)) := by
  change (Check.code (model := model) refs.first).eventTrace path.1 ++
    ((Check.code (model := model) refs.second).eventTrace path.2.1 ++
      ((FirstAccepted.circuit (model := model)
        (selectedInputs refs.first) refs.selection).eventTrace path.2.2.1 ++
        (FirstAccepted.circuit (model := model)
          (selectedInputs refs.second) refs.selection).eventTrace path.2.2.2)) = _
  rw [nativeQuadratic_check_eventTrace, nativeQuadratic_check_eventTrace]

/-- Every actual native coordinate is bounded by the independent twenty-instruction allowance. -/
lemma nativeQuadratic_pair_pool_le (refs : Refs ctx width) (path : (code (model := model)
  refs).Path) :
    (code (model := model) refs).resourcePool path ≤ nativeEnvelope (model := model) width := by
  rw [Circuit.resourcePool, nativeQuadratic_pair_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl
    (add_le_add (FirstAccepted.firstAccepted_pool_le _ _ path.2.2.1)
      (FirstAccepted.firstAccepted_pool_le _ _ path.2.2.2)))

/-- The independent native allowance contains exactly twenty instructions at every word width. -/
lemma nativeQuadratic_pair_nativeEnvelope_card (width : Nat) :
    (nativeEnvelope (model := model) width).card = 20 := rfl

/-- Actual total instructions count each real taken copy arm, after twelve unconditional checks. -/
lemma nativeQuadratic_pair_eventCount (refs : Refs ctx width) (path : (code (model := model)
  refs).Path) :
    ((code (model := model) refs).resourcePool path).card =
      12 + (if path.2.2.1.2.1.toBool then 4 else 2) +
        (if path.2.2.2.2.1.toBool then 4 else 2) := by
  rw [Circuit.resourcePool, nativeQuadratic_pair_eventTrace,
    FirstAccepted.firstAccepted_eventTrace, FirstAccepted.firstAccepted_eventTrace]
  change (checkEvents (model := model) width ++
    (checkEvents (model := model) width ++
      ((FirstAccepted.decisionEvents model ++
        (if path.2.2.1.2.1.toBool then FirstAccepted.copyEvents model width else [])) ++
      (FirstAccepted.decisionEvents model ++
        (if path.2.2.2.2.1.toBool then FirstAccepted.copyEvents model width else []))))).length = _
  split_ifs <;> rfl

/-- Unit native durations retain exactly the same actual serial instruction count. -/
lemma nativeQuadratic_pair_unitDepth (refs : Refs ctx width) (path : (code (model := model)
  refs).Path) :
    (code (model := model) refs).depth (fun _ => 1) path =
      12 + (if path.2.2.1.2.1.toBool then 4 else 2) +
        (if path.2.2.2.2.1.toBool then 4 else 2) := by
  change 6 + (6 +
    ((FirstAccepted.circuit (model := model) (selectedInputs refs.first) refs.selection).depth (fun
      _ => 1)
      path.2.2.1 +
    (FirstAccepted.circuit (model := model) (selectedInputs refs.second) refs.selection).depth (fun
      _ => 1)
      path.2.2.2)) = _
  rw [FirstAccepted.firstAccepted_unit_depth, FirstAccepted.firstAccepted_unit_depth]
  omega

/-- Both actual total events and unit-duration depth satisfy the same explicit upper bound. -/
lemma nativeQuadratic_pair_total_le (refs : Refs ctx width) (path : (code (model := model)
  refs).Path) :
    ((code (model := model) refs).resourcePool path).card ≤ 20 ∧
      (code (model := model) refs).depth (fun _ => 1) path ≤ 20 := by
  rw [nativeQuadratic_pair_eventCount, nativeQuadratic_pair_unitDepth]
  split_ifs <;> omega

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair
