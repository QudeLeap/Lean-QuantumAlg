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

variable {width : Nat} {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent six-operation trace for the two original Gram expressions. -/
def secondReductionInputsTrace (width : Nat) : List (Resource.Event model) :=
  ProductDifference.operationTrace (model := model) width ++
    ProductDifference.operationTrace (model := model) width

/-- Both actual product differences emit the six specified native operations. -/
lemma secondReductionInputsInto_events (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).eventTrace path =
      secondReductionInputsTrace (model := model) width := by
  unfold secondReductionInputsInto productDifferenceInto at path
  change
    (ProductDifference.computeInto (model := model) inputs.g11 inputs.g32 inputs.g31
      inputs.g21 refs.nu32 refs.nu32 refs.product).eventTrace path.1 ++
    (ProductDifference.computeInto (model := model) inputs.g11 inputs.g22 inputs.g21
      inputs.g21 refs.d32 refs.d32 refs.product).eventTrace path.2 = _
  rw [ProductDifference.computeInto_events, ProductDifference.computeInto_events]
  rfl

/-- Actual native multiplicity comes from the independent six-operation formula. -/
lemma secondReductionInputsInto_resourcePool (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).resourcePool path =
      ResourcePool.ofList (secondReductionInputsTrace (model := model) width) := by
  change ResourcePool.ofList
    ((secondReductionInputsInto (model := model) inputs refs).eventTrace path) = _
  rw [secondReductionInputsInto_events]

/-- All six actual native operations remain serially dependent. -/
lemma secondReductionInputsInto_depth (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).depth (fun _ => 1) path = 6 := rfl

/-- Both actual stages restore borrowed state jointly with every external quantum reference. -/
lemma secondReductionInputsInto_borrowedRestored
    (inputs : Inputs ctx width) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (secondReductionInputsInto (model := model) inputs refs).BorrowedRestored Reference state
      ((secondReductionInputsInto (model := model) inputs refs).execute environment
        Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (ProductDifference.computeInto_borrowedRestored _ _ _ _ _ _ _ Reference state)
    (ProductDifference.computeInto_borrowedRestored _ _ _ _ _ _ _ Reference _)

/-- All six operations visit the complete original supplied context. -/
lemma secondReductionInputsInto_visited (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).visitedContexts path =
      [ctx, ctx, ctx, ctx, ctx, ctx] := rfl

/-- Resident space retains every original quantum system and actual classical cell. -/
lemma secondReductionInputsInto_resident_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [secondReductionInputsInto_visited] at present
  have same : visited = ctx := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  rw [same]

/-- Auxiliary accounting includes the original shared product word throughout actual execution. -/
lemma secondReductionInputsInto_auxiliary_le (inputs : Inputs ctx width) (refs : Refs ctx width)
    (path : (secondReductionInputsInto (model := model) inputs refs).Path) :
    (secondReductionInputsInto (model := model) inputs refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [secondReductionInputsInto_visited] at present
  have same : visited = ctx := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
  rw [same]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeSecondReductionInputs
