/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix.Resources

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.PostReduction

/-!
# Actual final first-direction reduction resources

The original three stages have an independent native formula and a 24-operation
bound. Every original resident resource and borrowed correlation survives the
actual circuit, independently of the arithmetic input conditions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {width : Nat} {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent native formula for the final coefficient's three recorded sign decisions. -/
def postReductionTrace (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative : Bool) :
    List (Resource.Event model) :=
  LatticeSecondPairMachine.dotTrace (model := model) width ++
    (RoundedDiv.bodyTrace (model := model) width magnitudeNegative correctionNegative
      restoreNegative ++
      LatticeSecondPairMachine.reductionTrace (model := model) width)

/-- The actual path emits exactly the original three-stage native instruction sequence. -/
lemma postReductionInto_events (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    (postReductionInto (model := model) refs).eventTrace path =
      postReductionTrace (model := model) width
      path.2.1.1.1.2.1.toBool path.2.1.2.1.2.1.1.toBool path.2.1.2.2.2.2.1.toBool := by
  change _ ++ (_ ++ _) = _
  rw [LatticeDotRefresh.refreshInto_events, RoundedDiv.body_events,
    LatticeArithmetic.pointReduce_events]
  rfl

/-- Actual native multiplicity comes from the independently specified three-stage formula. -/
lemma postReductionInto_resourcePool (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    (postReductionInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (postReductionTrace (model := model) width
      path.2.1.1.1.2.1.toBool path.2.1.2.1.2.1.1.toBool path.2.1.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((postReductionInto (model := model) refs).eventTrace path) = _
  rw [postReductionInto_events]

/-- Every actual final-direction reduction uses at most 24 native classical operations. -/
lemma postReductionInto_eventCount_le (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    ((postReductionInto (model := model) refs).eventTrace path).length ≤ 24 := by
  have division := RoundedDiv.body_eventCount_le refs.machine.division31 path.2.1
  change List.length (_ ++ (_ ++ _)) ≤ 24
  simp only [List.length_append]
  change 5 +
    (((RoundedDiv.body (model := model) refs.machine.division31).eventTrace path.2.1).length +
      6) ≤ 24
  omega

/-- Unit-duration serial depth includes the actual dot, quotient and row-update dependencies. -/
lemma postReductionInto_depth_le (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    (postReductionInto (model := model) refs).depth (fun _ => 1) path ≤ 24 := by
  have division := RoundedDiv.body_depth_le refs.machine.division31 path.2.1
  change 5 +
    ((RoundedDiv.body (model := model) refs.machine.division31).depth (fun _ => 1) path.2.1 +
      6) ≤ 24
  omega

/-- Actual final-direction reduction restores the full borrowed-reference joint state. -/
lemma postReductionInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (postReductionInto (model := model) refs).BorrowedRestored Reference state
      ((postReductionInto (model := model) refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq (environment := environment)
    (LatticeDotRefresh.refreshInto (model := model)
      refs.machine.basis.third refs.machine.basis.first
      (refreshG31Refs refs)) (divisionReductionInto (model := model) refs)
  · exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference state
  · exact Circuit.borrowedRestored_seq (environment := environment) _ _ _
      (RoundedDiv.body_borrowedRestored refs.machine.division31 Reference _)
      (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)

/-- Every actual post-reduction phase retains the complete supplied live context. -/
lemma postReductionInto_visited (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (postReductionInto (model := model) refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with dot | division | reduction
  · rw [LatticeDotRefresh.refreshInto_visited] at dot
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using dot
  · exact RoundedDiv.body_visited refs.machine.division31 path.2.1 visited division
  · rw [LatticeArithmetic.pointReduce_visited] at reduction
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using reduction

/-- Resident space includes all original quantum systems and actual classical storage. -/
lemma postReductionInto_resident_le (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    (postReductionInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [postReductionInto_visited refs path visited present]

/-- Auxiliary space keeps every original role and scratch word counted throughout execution. -/
lemma postReductionInto_auxiliary_le (refs : Refs ctx width)
    (path : (postReductionInto (model := model) refs).Path) :
    (postReductionInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [postReductionInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairPostReduction
