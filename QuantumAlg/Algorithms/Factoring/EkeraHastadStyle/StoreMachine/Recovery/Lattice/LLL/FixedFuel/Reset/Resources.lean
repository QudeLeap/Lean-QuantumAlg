/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Reset

/-!
# Actual fixed-fuel initialization resources

Six original five-instruction Gram refreshes and two native XOR latch resets
execute in the original order. Their exact instruction sequence, depth and
live context come from that actual circuit, which also restores the complete
borrowed-reference joint state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent original two-XOR latch reset formula. -/
def resetFirstTrace : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .xor))]

/-- Independent original thirty-two-instruction initialization formula. -/
def refreshResetTrace (width : Nat) : List (Resource.Event model) :=
  LatticeMetricMachine.gramTrace (model := model) width ++ resetFirstTrace

/-- The actual two latch writes emit exactly the independent XOR formula. -/
theorem resetFirstInto_events (refs : Refs ctx width)
    (path : (resetFirstInto (model := model) refs).Path) :
    (resetFirstInto (model := model) refs).eventTrace path = resetFirstTrace := by
  change _ ++ _ = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual initialization emits the independent formula in the original chronological order. -/
theorem refreshResetInto_events (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    (refreshResetInto (model := model) refs).eventTrace path = refreshResetTrace width := by
  change _ ++ _ = _
  rw [LatticeMetricMachine.refreshInto_events, resetFirstInto_events]
  rfl

/-- Actual initialization multiplicities are exactly the independent native formula. -/
theorem refreshResetInto_resourcePool (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    (refreshResetInto (model := model) refs).resourcePool path =
      ResourcePool.ofList (refreshResetTrace width) :=
  congrArg ResourcePool.ofList (refreshResetInto_events refs path)

/-- Exactly thirty-two native classical instructions execute in every initialization path. -/
theorem refreshResetInto_eventCount (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    ((refreshResetInto (model := model) refs).eventTrace path).length = 32 := rfl

/-- The original chronological initialization has unit-duration dependency depth thirty-two. -/
theorem refreshResetInto_depth (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    (refreshResetInto (model := model) refs).depth (fun _ => 1) path = 32 := rfl

/-- Both actual latch resets restore the complete borrowed-reference joint state. -/
theorem resetFirstInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (resetFirstInto (model := model) refs).BorrowedRestored Reference state
      ((resetFirstInto (model := model) refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical _ state) (Circuit.borrowedRestored_classical _ _)

/-- Gram refresh followed by both resets restores all original borrowed-reference correlations. -/
theorem refreshResetInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (refreshResetInto (model := model) refs).BorrowedRestored Reference state
      ((refreshResetInto (model := model) refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeMetricMachine.refreshInto_borrowedRestored _ _ Reference state)
    (resetFirstInto_borrowedRestored refs Reference _)

/-- Every initialization instruction uses the complete supplied live context. -/
theorem refreshResetInto_visited (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (refreshResetInto (model := model) refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with gram | reset
  · rw [LatticeMetricMachine.refreshInto_visited] at gram
    exact (List.mem_replicate.mp gram).2
  · change visited ∈ [ctx, ctx] at reset
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using reset

/-- All original resident resources are counted throughout initialization. -/
theorem refreshResetInto_resident_le (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    (refreshResetInto (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [refreshResetInto_visited refs path visited present]

/-- All original auxiliary roles are counted throughout initialization. -/
theorem refreshResetInto_auxiliary_le (refs : Refs ctx width)
    (path : (refreshResetInto (model := model) refs).Path) :
    (refreshResetInto (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [refreshResetInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
