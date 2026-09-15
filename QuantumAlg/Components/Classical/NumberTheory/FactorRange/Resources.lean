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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exact native coordinates of the two real comparisons and their stored conjunction. -/
def events (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .lessThan width),
    .classicalOperation (.wordBinary .lessThan width), .classicalOperation (.bit .and)]

/-- Independent literal native budget of the same three closed instructions. -/
def eventBudget (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  ResourcePool.ofList (events kind width)

/-- Every actual check executes both comparisons and the final conjunction exactly once. -/
theorem code_eventTrace (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).eventTrace path = events kind width := rfl

/-- The real event multiset equals the independent literal budget in every native coordinate. -/
theorem code_pool (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).resourcePool path = eventBudget kind width := rfl

/-- The conjunction depends on both real comparison writes, giving exactly three unit steps. -/
theorem code_unitDepth (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).depth (fun _ => 1) path = 3 := rfl

/-- All three instructions visit the same actual live context and allocate no new storage. -/
theorem code_visited (refs : Refs ctx width) (path : (code refs).Path)
    (visited : RuntimeCtx kind) (present : visited ∈ (code refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx, ctx, ctx] at present
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present

/-- The actual resident peak contains exactly the frame already provided by the caller. -/
theorem code_resident_le (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (code_visited refs path visited present) ▸ le_rfl

/-- Every original auxiliary role is retained and no further scratch is introduced. -/
theorem code_auxiliary_le (refs : Refs ctx width) (path : (code refs).Path) :
    (code refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (code_visited refs path visited present) ▸ le_rfl

end QuantumAlg.ClassicalRoutines.NumberTheory.FactorRange
