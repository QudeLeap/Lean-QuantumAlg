/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Prefix

/-!
# Actual second-pair prefix resources

The original five stages have an independent native instruction formula and a
35-operation bound. All supplied live resources and borrowed correlations
remain accounted for throughout the actual circuit execution.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native dot-refresh formula, including its initial overwrite. -/
def dotTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .add width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .add width)]

/-- Independent native formula for reducing all three coordinates of one row. -/
def reductionTrace (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width),
    .classicalOperation (.wordBinary .mulLow width), .classicalOperation (.wordBinary .sub width)]

/-- Independent chronological formula for the three recorded division decisions. -/
def secondPairPrefixTrace (width : Nat)
    (magnitudeNegative correctionNegative restoreNegative : Bool) :
    List (Resource.Event kind) :=
  (dotTrace width ++
    (dotTrace width ++ LatticeSecondReductionInputs.secondReductionInputsTrace width))
    ++ (RoundedDiv.bodyTrace width magnitudeNegative correctionNegative restoreNegative ++
      reductionTrace width)

/-- The actual path emits exactly the independent five-stage native instruction sequence. -/
theorem secondPairPrefixInto_events (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    (secondPairPrefixInto refs).eventTrace path = secondPairPrefixTrace width
      path.2.1.1.1.2.1.toBool path.2.1.2.1.2.1.1.toBool path.2.1.2.2.2.2.1.toBool := by
  change (_ ++ (_ ++ _)) ++ (_ ++ _) = _
  rw [LatticeDotRefresh.refreshInto_events, LatticeDotRefresh.refreshInto_events,
    LatticeSecondReductionInputs.secondReductionInputsInto_events,
    RoundedDiv.body_events, LatticeArithmetic.pointReduce_events]
  rfl

/-- Actual native multiplicity is computed from the independently specified event sequence. -/
theorem secondPairPrefixInto_resourcePool (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    (secondPairPrefixInto refs).resourcePool path = ResourcePool.ofList (secondPairPrefixTrace width
      path.2.1.1.1.2.1.toBool path.2.1.2.1.2.1.1.toBool path.2.1.2.2.2.2.1.toBool) := by
  change ResourcePool.ofList ((secondPairPrefixInto refs).eventTrace path) = _
  rw [secondPairPrefixInto_events]

/-- Every actual prefix path executes at most 35 native classical instructions. -/
theorem secondPairPrefixInto_eventCount_le (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    ((secondPairPrefixInto refs).eventTrace path).length ≤ 35 := by
  have division := RoundedDiv.body_eventCount_le refs.division32 path.2.1
  change List.length ((_ ++ (_ ++ _)) ++ (_ ++ _)) ≤ 35
  simp only [List.length_append]
  change 5 + (5 + 6) + (((RoundedDiv.body refs.division32).eventTrace path.2.1).length + 6) ≤ 35
  omega

/-- Unit-duration serial depth includes all dependencies on actual earlier writes and decisions. -/
theorem secondPairPrefixInto_depth_le (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    (secondPairPrefixInto refs).depth (fun _ => 1) path ≤ 35 := by
  have division := RoundedDiv.body_depth_le refs.division32 path.2.1
  change 5 + (5 + 6) + ((RoundedDiv.body refs.division32).depth (fun _ => 1) path.2.1 + 6) ≤ 35
  omega

/-- Actual prefix execution restores all borrowed correlations jointly with external references. -/
theorem secondPairPrefixInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (secondPairPrefixInto refs).BorrowedRestored Reference state
      ((secondPairPrefixInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_seq (refreshInputsInto refs) (divisionReductionInto refs)
  · apply Circuit.borrowedRestored_seq
      (LatticeDotRefresh.refreshInto refs.basis.second refs.basis.first (refreshG21Refs refs))
      (refresh32InputsInto refs)
    · exact LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference state
    · exact Circuit.borrowedRestored_seq _ _ _
        (LatticeDotRefresh.refreshInto_borrowedRestored _ _ _ Reference _)
        (LatticeSecondReductionInputs.secondReductionInputsInto_borrowedRestored _ _ Reference _)
  · exact Circuit.borrowedRestored_seq _ _ _
      (RoundedDiv.body_borrowedRestored refs.division32 Reference _)
      (LatticeArithmetic.pointReduce_borrowedRestored _ _ _ _ Reference _)

/-- Every actual prefix phase uses the complete supplied context without hidden allocation. -/
theorem secondPairPrefixInto_visited (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (secondPairPrefixInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ ((_ ++ (_ ++ _)) ++ (_ ++ _)) at present
  simp only [List.mem_append] at present
  rcases present with (firstDot | secondDot | inputs) | division | reduction
  · rw [LatticeDotRefresh.refreshInto_visited] at firstDot
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using firstDot
  · rw [LatticeDotRefresh.refreshInto_visited] at secondDot
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using secondDot
  · rw [LatticeSecondReductionInputs.secondReductionInputsInto_visited] at inputs
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using inputs
  · exact RoundedDiv.body_visited refs.division32 path.2.1 visited division
  · rw [LatticeArithmetic.pointReduce_visited] at reduction
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using reduction

/-- Resident space counts every supplied quantum system and actual classical cell. -/
theorem secondPairPrefixInto_resident_le (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    (secondPairPrefixInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [secondPairPrefixInto_visited refs path visited present]

/-- Auxiliary accounting preserves all caller roles and counts every scratch cell throughout. -/
theorem secondPairPrefixInto_auxiliary_le (refs : Refs ctx width)
    (path : (secondPairPrefixInto refs).Path) :
    (secondPairPrefixInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [secondPairPrefixInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondPairMachine
