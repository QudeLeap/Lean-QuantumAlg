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

/-- The actual decoder and complete final manifest, reading the newly written word. -/
def run {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat)
    (order : BitOrder) (input : CInputRef ctx (InputShape width))
    (key : StorageKey) (fresh : key ∉ ctx.keys) :
    AlgorithmRun ctx (ResultCtx ctx width key fresh) (OutputShape width) where
  code := routine ctx width order input key fresh
  output := Output.all (ResultCtx ctx width key fresh)
    (.read (resultRef ctx width key fresh))

/-- No original entry or retained result is omitted from the complete output. -/
theorem terminalDecode_run_output_listing {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys) :
    (run ctx width order input key fresh).output.listing =
      (ResultCtx ctx width key fresh).keys := rfl

/-- The retained allocation leaves the literal two-coordinate decoder budget unchanged. -/
theorem terminalDecode_routine_pool_le {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine ctx width order input key fresh).Path) :
    (routine ctx width order input key fresh).resourcePool path ≤ envelope width := by
  change (intoFromBitRefs order
    (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).resourcePool path.2 ≤ _
  exact terminalDecode_intoFromBitRefs_pool_le order _ _ path.2

/-- Every path has at most the stated fixed-width shift-and-increment duration. -/
theorem terminalDecode_routine_depth_le {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (duration : Resource.Event kind → Nat)
    (path : (routine ctx width order input key fresh).Path) :
    (routine ctx width order input key fresh).depth duration path ≤
      width * (duration (shiftEvent width) + duration (incrementEvent width)) := by
  change 0 + (intoFromBitRefs order
    (fun bit => .bitsGet (input.underRetained key (OutputShape width) fresh) bit)
    (CWriteRef.retainedHead ctx key (OutputShape width) fresh)).depth duration path.2 ≤ _
  rw [Nat.zero_add]
  exact terminalDecode_intoFromBitRefs_depth_le order _ _ duration path.2

private theorem routine_visited_cases {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine ctx width order input key fresh).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (routine ctx width order input key fresh).visitedContexts path) :
    visited = ctx ∨ visited = ResultCtx ctx width key fresh := by
  change visited ∈ [ctx, ResultCtx ctx width key fresh] ++
    (into order (input.underRetained key (OutputShape width) fresh)
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
theorem terminalDecode_routine_resident_le {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine ctx width order input key fresh).Path) :
    (routine ctx width order input key fresh).peakResidentSpace path ≤
      (ResultCtx ctx width key fresh).residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rcases routine_visited_cases ctx width order input key fresh path visited present with
    original | extended
  · subst visited
    intro axis
    cases axis <;> simp [ResultCtx]
  · exact extended ▸ le_rfl

/-- The retained word is included in the actual auxiliary peak bound. -/
theorem terminalDecode_routine_auxiliary_le {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) (order : BitOrder)
    (input : CInputRef ctx (InputShape width)) (key : StorageKey) (fresh : key ∉ ctx.keys)
    (path : (routine ctx width order input key fresh).Path) :
    (routine ctx width order input key fresh).peakAuxiliarySpace path ≤
      (ResultCtx ctx width key fresh).auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rcases routine_visited_cases ctx width order input key fresh path visited present with
    original | extended
  · subst visited
    intro axis
    cases axis <;> simp [ResultCtx]
  · exact extended ▸ le_rfl

end QuantumAlg.ClassicalRoutines.TerminalDecode
