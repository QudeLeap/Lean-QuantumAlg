/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Complete retained terminal-decoder run and native bounds

The run allocates one actual result word, executes the same decoder, and lists
every final live key. Allocation emits no classical arithmetic event. The
independent event and duration bounds are the fixed source-width allowance
for shifts and increments; resident and auxiliary limits include the retained
word and the complete original context at every physical dimension.
-/

namespace QuantumAlg.ClassicalRoutines.TerminalDecode

open ClassicalAlgorithms.TerminalDecode

noncomputable section

/-- The actual decoder and complete final manifest, reading the newly written word. -/
def run {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat)
    (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    AlgorithmRun model ctx (ResultCtx ctx width key fresh) (OutputShape width) where
  code := routine (model := model) ctx width order input key fresh
  output := Output.all (ResultCtx ctx width key fresh)
    (.read (resultRef ctx width key fresh))

/-- No original entry or retained result is omitted from the complete output. -/
theorem terminalDecode_run_output_listing {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (run (model := model) ctx width order input key fresh).output.listing =
      (ResultCtx ctx width key fresh).keys := rfl

/-- The retained allocation leaves the literal two-coordinate decoder budget unchanged. -/
theorem terminalDecode_routine_pool_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine (model := model) ctx width order input key fresh).Path) :
    (routine (model := model) ctx width order input key fresh).resourcePool path ≤
      envelope (model := model) width := by
  change (intoFromBitRefs (model := model) order
    (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).resourcePool path.2 ≤ _
  exact terminalDecode_intoFromBitRefs_pool_le order _ _ path.2

/-- Every path has at most the stated fixed-width shift-and-increment duration. -/
theorem terminalDecode_routine_depth_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (duration : Resource.Event model → Nat)
    (path : (routine (model := model) ctx width order input key fresh).Path) :
    (routine (model := model) ctx width order input key fresh).depth duration path ≤
      width * (duration (shiftEvent (model := model) width) +
        duration (incrementEvent (model := model) width)) := by
  change 0 + (intoFromBitRefs (model := model) order
    (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).depth duration path.2 ≤ _
  rw [Nat.zero_add]
  exact terminalDecode_intoFromBitRefs_depth_le order _ _ duration path.2

private theorem routine_visited_cases {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine (model := model) ctx width order input key fresh).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈
      (routine (model := model) ctx width order input key fresh).visitedContexts path) :
    visited = ctx ∨ visited = ResultCtx ctx width key fresh := by
  change visited ∈ [ctx, ResultCtx ctx width key fresh] ++
    (into (model := model) order (input.underRetained key (OutputShape width) fresh)
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with allocation | decoding
  · simpa only [List.mem_cons, List.not_mem_nil, or_false] using allocation
  · exact Or.inr (terminalDecode_fold_visited
      (CWriteRef.retainedHead ctx key (OutputShape width) fresh)
      (List.ofFn (fun index => .bitsGet
        (input.underRetained key (OutputShape width) fresh) (sourceIndex order index)))
      path.2 visited decoding)

/-- Resident storage is bounded by the complete context including the new retained word. -/
theorem terminalDecode_routine_resident_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine (model := model) ctx width order input key fresh).Path) :
    (routine (model := model) ctx width order input key fresh).peakResidentSpace path ≤
      (ResultCtx ctx width key fresh).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases routine_visited_cases ctx width order input key fresh path visited present with
    original | extended
  · subst visited
    intro axis
    change ctx.residentSpace axis ≤
      SpacePool.ofShape (OutputShape width) axis + ctx.residentSpace axis
    exact Nat.le_add_left _ _
  · exact extended ▸ le_rfl

/-- The retained word is included in the actual auxiliary peak bound. -/
theorem terminalDecode_routine_auxiliary_le {model : ExecutionModel} [BitWord.Selected model]
    (ctx : RuntimeCtx model.kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine (model := model) ctx width order input key fresh).Path) :
    (routine (model := model) ctx width order input key fresh).peakAuxiliarySpace path ≤
      (ResultCtx ctx width key fresh).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases routine_visited_cases ctx width order input key fresh path visited present with
    original | extended
  · subst visited
    intro axis
    change ctx.auxiliarySpace axis ≤
      SpacePool.ofShape (OutputShape width) axis + ctx.auxiliarySpace axis
    exact Nat.le_add_left _ _
  · exact extended ▸ le_rfl

end

end QuantumAlg.ClassicalRoutines.TerminalDecode
