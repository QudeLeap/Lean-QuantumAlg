/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Base.Accounting.Context

/-!
# Actual live storage during terminal splitting

Every decoder, resize and shift visits the same one-word extension of the
original context. Its lexical wrapper additionally visits the original
context on entry and exit. Thus both live-space peaks add only the one real
full-index classical word, while all original quantum systems remain counted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

private theorem shifts_visited {width : Nat} (count : Nat)
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (TerminalShift.code count output).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (TerminalShift.code count output).visitedContexts path) :
    visited = ctx := by
  change visited ∈ ctx :: (List.ofFn (fun _ : Fin count => [ctx])).flatten at present
  rw [TerminalShift.flatten_repeated_singleton] at present
  rcases List.mem_cons.mp present with same | repeated
  · exact same
  · exact (List.mem_replicate.mp repeated).2

/-- Every actual extraction-body visit is to its one real full-index-word context. -/
theorem nativeRecovery_terminal_split_body_visited
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (body input refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (body input refs).visitedContexts path) :
    visited = context ctx m ell := by
  change visited ∈
    (terminalCircuit (underRead input m ell) (full ctx m ell)).visitedContexts path.1 ++
      ([context ctx m ell] ++
        ((TerminalShift.code ell (full ctx m ell)).visitedContexts path.2.2.1 ++
          [context ctx m ell])) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with decoded | same | shifted | same
  · exact TerminalDecode.terminalDecode_fold_visited (full ctx m ell)
      (List.ofFn (fun index => CInputRef.bitsGet (underRead input m ell) index))
      path.1 visited decoded
  · exact same
  · exact shifts_visited ell (full ctx m ell) path.2.2.1 visited shifted
  · exact same

/-- Entry, execution and reverse release visit only the original context and its actual extension.
-/
theorem nativeRecovery_terminal_split_visited
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (code input refs).Path) (visited : RuntimeCtx kind)
    (present : visited ∈ (code input refs).visitedContexts path) :
    visited = ctx ∨ visited = context ctx m ell := by
  change visited ∈ ctx :: (body input refs).visitedContexts path ++ [ctx] at present
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with (same | middle) | same
  · exact Or.inl same
  · exact Or.inr (nativeRecovery_terminal_split_body_visited input refs path visited middle)
  · exact Or.inl same

/-- Both actual peaks count the original context and exactly one additional full-index word. -/
theorem nativeRecovery_terminal_split_space_le
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (code input refs).Path) :
    (code input refs).peakResidentSpace path ≤
        SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) + ctx.residentSpace ∧
      (code input refs).peakAuxiliarySpace path ≤
        SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) + ctx.auxiliarySpace := by
  have residentCaller : ctx.residentSpace ≤
      SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) + ctx.residentSpace := by
    intro axis
    change ctx.residentSpace axis ≤
      SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) axis + ctx.residentSpace axis
    omega
  have auxiliaryCaller : ctx.auxiliarySpace ≤
      SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) + ctx.auxiliarySpace := by
    intro axis
    change ctx.auxiliarySpace axis ≤
      SpacePool.ofShape (.unsignedWord ((ell + m) + ell)) axis + ctx.auxiliarySpace axis
    omega
  constructor
  · apply Circuit.peakResidentSpace_le_of_visited
    intro visited present
    rcases nativeRecovery_terminal_split_visited input refs path visited present with rfl | rfl
    · exact residentCaller
    · exact le_rfl
  · apply Circuit.peakAuxiliarySpace_le_of_visited
    intro visited present
    rcases nativeRecovery_terminal_split_visited input refs path visited present with rfl | rfl
    · exact auxiliaryCaller
    · exact le_rfl

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
