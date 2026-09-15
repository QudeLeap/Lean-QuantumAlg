/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.SecondPair.Inputs

/-!
# Actual second-reduction input resources

The actual circuit contains six native instructions and no allocation. Borrowed
restoration is independent of any arithmetic or initial scratch premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent six-operation trace for the two original Gram expressions. -/
def secondReductionInputsTrace (width : Nat) : List (Resource.Event kind) :=
  ProductDifference.operationTrace width ++ ProductDifference.operationTrace width

/-- Both actual product differences emit the six specified native operations. -/
theorem secondReductionInputsInto_events (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).eventTrace path =
      secondReductionInputsTrace width := rfl

/-- Actual native multiplicity comes from the independent six-operation formula. -/
theorem secondReductionInputsInto_resourcePool (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).resourcePool path =
      ResourcePool.ofList (secondReductionInputsTrace width) := rfl

/-- All six actual native operations remain serially dependent. -/
theorem secondReductionInputsInto_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).depth (fun _ => 1) path = 6 := rfl

/-- Both actual stages restore borrowed state jointly with every external quantum reference. -/
theorem secondReductionInputsInto_borrowedRestored
    (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (secondReductionInputsInto inputs refs).BorrowedRestored Reference state
      ((secondReductionInputsInto inputs refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (ProductDifference.computeInto_borrowedRestored _ _ _ _ _ _ _ Reference state)
    (ProductDifference.computeInto_borrowedRestored _ _ _ _ _ _ _ Reference _)

/-- All six operations visit the complete original supplied context. -/
theorem secondReductionInputsInto_visited (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- Resident space retains every original quantum system and actual classical cell. -/
theorem secondReductionInputsInto_resident_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [secondReductionInputsInto_visited] at present
  have same : visited = ctx := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  rw [same]

/-- Auxiliary accounting includes the original shared product word throughout actual execution. -/
theorem secondReductionInputsInto_auxiliary_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto inputs refs).Path) :
    (secondReductionInputsInto inputs refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [secondReductionInputsInto_visited] at present
  have same : visited = ctx := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  rw [same]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs
