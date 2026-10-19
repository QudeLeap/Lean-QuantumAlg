/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Circuit
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete borrowed restoration of native saturating subtraction

The actual comparison and both actual branches write only intrinsically
writable classical cells. Their syntax composes complete borrowed restoration
through dispatch and lexical release. All borrowed classical and quantum
systems retain their joint state with any external reference; no absence of
borrowed quantum wires or independence assumption is needed.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub

open Execution

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Both real output instructions restore the complete borrowed interface in each selected fiber. -/
lemma nativeSub_selected_borrowedRestored
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx) Reference (model.HiddenState × History)) :
    (selected (model := model) left right output value).BorrowedRestored Reference state
      ((selected (model := model) left right output value).execute environment
        Reference state) := by
  cases value with
  | bit flag =>
      cases flag
      · exact Circuit.borrowedRestored_classical (environment := environment) _ state
      · exact Circuit.borrowedRestored_classical (environment := environment) _ state

/-- The real comparison and its true stored-value branch restore all borrowed correlations. -/
lemma nativeSub_body_borrowedRestored (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference (model.HiddenState ×
      History)) :
    (body (model := model) left right output).BorrowedRestored Reference state
      ((body (model := model) left right output).execute environment Reference state) := by
  apply Circuit.borrowedRestored_seq
  · exact Circuit.borrowedRestored_classical (environment := environment) _ state
  · apply Circuit.borrowedRestored_branch (environment := environment)
    intro value _history _ current
    exact nativeSub_selected_borrowedRestored left right output value Reference current

/-- The one real lexical flag is released while all original borrowed systems return jointly. -/
lemma nativeSub_into_borrowedRestored (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (into (model := model) left right output).BorrowedRestored Reference state
      ((into (model := model) left right output).execute environment Reference state) :=
  Circuit.borrowedRestored_workspace
    (environment := environment) ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (body (model := model) left right output) Reference
    (fun {_} _ initial => nativeSub_body_borrowedRestored left right output Reference initial) state

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
