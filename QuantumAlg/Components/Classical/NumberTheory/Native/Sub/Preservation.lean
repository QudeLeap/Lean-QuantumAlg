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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Both real output instructions restore the complete borrowed interface in each selected fiber. -/
theorem nativeSub_selected_borrowedRestored
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (value : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx) Reference History) :
    (selected left right output value).BorrowedRestored Reference state
      ((selected left right output value).execute Reference state) := by
  cases value with
  | bit flag =>
      cases flag
      · exact Circuit.borrowedRestored_classical (subtractOp left right output) state
      · exact Circuit.borrowedRestored_classical (clearOp output) state

/-- The real comparison and its true stored-value branch restore all borrowed correlations. -/
theorem nativeSub_body_borrowedRestored (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State (context ctx) Reference History) :
    (body left right output).BorrowedRestored Reference state
      ((body left right output).execute Reference state) :=
  Circuit.borrowedRestored_seq (.classical (compareOp left right))
    (.branch (.storage (decision ctx).toCStorageRef) (selected left right output)) state
    (Circuit.borrowedRestored_classical (compareOp left right) state)
    (Circuit.borrowedRestored_branch (.storage (decision ctx).toCStorageRef)
      (selected left right output) Reference
      (fun value {_} _ initial =>
        nativeSub_selected_borrowedRestored left right output value Reference initial) _)

/-- The one real lexical flag is released while all original borrowed systems return jointly. -/
theorem nativeSub_into_borrowedRestored (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into left right output).BorrowedRestored Reference state
      ((into left right output).execute Reference state) :=
  Circuit.borrowedRestored_workspace ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh
    (body left right output) Reference
    (fun {_} _ initial => nativeSub_body_borrowedRestored left right output Reference initial) state

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSub
