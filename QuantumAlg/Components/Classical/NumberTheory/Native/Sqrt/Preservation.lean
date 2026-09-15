/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Semantics
import all QuantumAlg.Components.Classical.ConstantWord.Preservation
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Complete borrowed restoration of the actual native square root

Every actual instruction writes an intrinsically writable cell. The literal
loader, selected rounds and final copy preserve the complete ordered borrowed
classical value; the matching scope pushes and pops preserve that same value.
The proved full-state equation consequently restores all borrowed classical
and quantum systems jointly with every external reference, without assuming
that the incoming state or any of its stored values is independent.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem select_borrowed (refs : RoundRefs ctx width) (store : Store ctx) :
    (selectStep refs store).1.readBorrowedClassical = store.readBorrowedClassical := by
  unfold selectStep
  cases flagRead : store.read (.storage refs.tooLarge.toCStorageRef) with
  | bit flag =>
      cases flag with
      | false => exact Store.readBorrowedClassical_applyOp store (copyOp refs)
      | true => rfl

/-- Every actual round preserves the complete actual borrowed classical tuple. -/
theorem nativeSqrt_round_borrowed_values
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (store : Store ctx) :
    (roundStep input refs store).1.readBorrowedClassical = store.readBorrowedClassical := by
  simp only [roundStep, Store.readBorrowedClassical_applyOp, select_borrowed]

/-- The true finite round schedule keeps every borrowed classical value at every count. -/
theorem nativeSqrt_iteration_borrowed_values
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : RoundRefs ctx width)
    (count : Nat) (store : Store ctx) :
    (iteratedRoundStep input refs count store).1.readBorrowedClassical =
      store.readBorrowedClassical := by
  change ((fun current => (roundStep input refs current).1)^[count] store).readBorrowedClassical = _
  induction count generalizing store with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact (inductionHypothesis _).trans (nativeSqrt_round_borrowed_values input refs store)

/-- Widening, literal initialization, real rounds and final output all preserve borrowed values. -/
theorem nativeSqrt_body_borrowed_values (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store (context ctx width)) :
    (bodyStep input output store).1.readBorrowedClassical = store.readBorrowedClassical := by
  simp only [bodyStep, Store.readBorrowedClassical_applyOp, nativeSqrt_iteration_borrowed_values,
    ConstantWord.constantWord_foldStep_borrowed_values]

private theorem push_borrowed (width : Nat) (store : Store ctx) :
    (pushStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

private theorem pop_borrowed (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).readBorrowedClassical = store.readBorrowedClassical := rfl

/-- The actual matched lexical releases return the complete original borrowed classical tuple. -/
theorem nativeSqrt_into_borrowed_values (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    (intoStep input output store).1.readBorrowedClassical = store.readBorrowedClassical :=
  (pop_borrowed width (bodyStep input output (pushStore width store)).1).trans
    ((nativeSqrt_body_borrowed_values input output (pushStore width store)).trans
      (push_borrowed width store))

private theorem restored_of_equation (program : Circuit ctx ctx)
    (update : Store ctx → Store ctx × program.Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      program.execute Reference state = state.mapClassical (fun entry =>
        ((update entry.1).1, (entry.2, (update entry.1).2))))
    (preserves : ∀ store, (update store).1.readBorrowedClassical = store.readBorrowedClassical)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    program.BorrowedRestored Reference state (program.execute Reference state) := by
  rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, equation]
  refine Eq.trans ?_ (observeBorrowed_mapClassical (ctx := ctx) (Reference := Reference)
    (H := History) (K := History × program.Path) state
    (fun entry => ((update entry.1).1, (entry.2, (update entry.1).2)))
    (fun entry => preserves entry.1))
  congr 1
  congr 1
  exact Subsingleton.elim _ _

/-- All borrowed classical and quantum systems return jointly with every external reference. -/
theorem nativeSqrt_into_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into input output).BorrowedRestored Reference state
      ((into input output).execute Reference state) :=
  restored_of_equation (into input output) (intoStep input output)
    (nativeSqrt_into_execute input output) (nativeSqrt_into_borrowed_values input output)
    Reference state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
