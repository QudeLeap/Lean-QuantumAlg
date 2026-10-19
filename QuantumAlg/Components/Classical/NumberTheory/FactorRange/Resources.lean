/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.FactorRange
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual native resources of the stored factor range check

The real two unsigned comparisons and their stored conjunction are three
serial native events. They use only the supplied physical references in the
existing context. Their exact ledger and unchanged live-space bounds can be
composed by every actual factor-recovery consumer of this single circuit.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.FactorRange

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Exact native coordinates of the two real comparisons and their stored conjunction. -/
def events (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Independent literal native budget of the same three closed instructions. -/
def eventBudget (width : Nat) : ResourcePool model :=
  ResourcePool.ofList (events (model := model) width)

/-- Every actual check executes both comparisons and the final conjunction exactly once. -/
lemma code_eventTrace (refs : Refs ctx width) (path : (code (model := model) refs).Path) :
    (code (model := model) refs).eventTrace path = events (model := model) width := by
  change (BitWord.instruction (execution := model) (lowerOp refs)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (upperOp refs)).eventTrace path.2.1 ++
      (BitWord.instruction (execution := model) (combineOp refs)).eventTrace path.2.2) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The real event multiset equals the independent literal budget in every native coordinate. -/
lemma code_pool (refs : Refs ctx width) (path : (code (model := model) refs).Path) :
    (code (model := model) refs).resourcePool path = eventBudget (model := model) width := by
  unfold Circuit.resourcePool eventBudget
  rw [code_eventTrace]

/-- The conjunction depends on both real comparison writes, giving exactly three unit steps. -/
lemma code_unitDepth (refs : Refs ctx width) (path : (code (model := model) refs).Path) :
    (code (model := model) refs).depth (fun _ => 1) path = 3 := rfl

/-- All three instructions visit the same actual live context and allocate no new storage. -/
lemma code_visited (refs : Refs ctx width) (path : (code (model := model) refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (code (model := model) refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx, ctx, ctx] at present
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- The actual resident peak contains exactly the frame already provided by the caller. -/
lemma code_resident_le (refs : Refs ctx width) (path : (code (model := model) refs).Path) :
    (code (model := model) refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (code_visited refs path visited present) ▸ le_rfl

/-- Every original auxiliary role is retained and no further scratch is introduced. -/
lemma code_auxiliary_le (refs : Refs ctx width) (path : (code (model := model) refs).Path) :
    (code (model := model) refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (code_visited refs path visited present) ▸ le_rfl

end

end QuantumAlg.ClassicalRoutines.NumberTheory.FactorRange
