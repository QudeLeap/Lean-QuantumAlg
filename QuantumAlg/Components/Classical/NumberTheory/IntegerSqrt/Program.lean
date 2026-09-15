/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.IntegerSqrt.Layout
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual binary integer-square-root refinement round
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Carrying addition that constructs the candidate midpoint. -/
def addOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :=
  ClassicalOp.addCarry width ctx
    (.product (writeInput refs.root) (writeInput refs.half)) refs.midCarry

/-- Full-width square of the candidate midpoint. -/
def squareOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) :=
  ClassicalOp.mulFull width width ctx
    (.product (.first (writeInput refs.midCarry)) (.first (writeInput refs.midCarry))) refs.square

/-- Comparison of the input with the squared candidate midpoint. -/
def compareOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (input : CInputRef ctx (.unsignedWord (width + width))) (refs : Refs ctx width) :=
  ClassicalOp.wordBinary .lessThan (width + width) ctx
    (.product input (writeInput refs.square)) refs.tooLarge

/-- Negation of the too-large flag used as the candidate-selection bit. -/
def takeOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat} (refs : Refs ctx width) :=
  ClassicalOp.bit .not ctx (writeInput refs.tooLarge) refs.take

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The selected root copy uses the midpoint or the original root according to the stored flag. -/
def rootOp (refs : Refs ctx width) (take : Bool) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx
    (if take then .first (writeInput refs.midCarry) else writeInput refs.root) refs.root

/-- The original half increment is divided by two with one native right shift. -/
def halfOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .shiftRight width ctx (writeInput refs.half) refs.half

/-- Four native writes compute the candidate midpoint, square, comparison and selection flag. -/
def roundPrefixInto (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (addOp refs))
    (.seq (.classical (squareOp refs))
      (.seq (.classical (compareOp input refs)) (.classical (takeOp refs))))

/-- The chronological actual prefix store and its four native instruction paths. -/
def roundPrefixStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (roundPrefixInto input refs).Path :=
  ((((store.applyOp (addOp refs)).applyOp (squareOp refs)).applyOp
    (compareOp input refs)).applyOp (takeOp refs), ((), ((), ((), ()))))

/-- The four original writes preserve every history and the full quantum-reference state. -/
theorem roundPrefixInto_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (roundPrefixInto input refs).execute Reference state = state.mapClassical (fun entry =>
      ((roundPrefixStep input refs entry.1).1,
        (entry.2, (roundPrefixStep input refs entry.1).2))) := by
  simp only [roundPrefixInto, roundPrefixStep, Circuit.execute_seq,
    Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The actual take-cell read dispatches the original root-copy instruction. -/
def rootInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.take) fun value => .classical (rootOp refs value.toBool)

/-- The root store and recorded flag come from the same actual incoming state. -/
def rootStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (rootInto refs).Path :=
  let flag := store.read (writeInput refs.take)
  (store.applyOp (rootOp refs flag.toBool), ⟨flag, ()⟩)

/-- The actual stored flag selects the executed copy and is retained in its path. -/
theorem rootInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (rootInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((rootStep refs entry.1).1, (entry.2, (rootStep refs entry.1).2))) := by
  exact Circuit.execute_branch_mapClassical (writeInput refs.take)
    (fun value => .classical (rootOp refs value.toBool))
    (fun value store => (store.applyOp (rootOp refs value.toBool), ()))
    (by
      intro value Reference history _ current
      refine (Circuit.execute_classical_mapClassical (rootOp refs value.toBool)
        Reference current).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state

/-- The original four-write prefix, stored-flag root copy and native half shift. -/
def roundInto (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (roundPrefixInto input refs) (.seq (rootInto refs) (.classical (halfOp refs)))

/-- Complete actual final store and chronological path of the original refinement round. -/
def roundStep (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (store : Store ctx) : Store ctx × (roundInto input refs).Path :=
  let prefixResult := roundPrefixStep input refs store
  let root := rootStep refs prefixResult.1
  (root.1.applyOp (halfOp refs), (prefixResult.2, (root.2, ())))

/-- Complete real execution retains prior histories and all original quantum-reference blocks. -/
theorem roundInto_execute (input : CInputRef ctx (.unsignedWord (width + width)))
    (refs : Refs ctx width) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (roundInto input refs).execute Reference state = state.mapClassical (fun entry =>
      ((roundStep input refs entry.1).1, (entry.2, (roundStep input refs entry.1).2))) := by
  simp only [roundInto, roundStep, Circuit.execute_seq, roundPrefixInto_execute,
    rootInto_execute, Circuit.execute_classical_mapClassical, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.IntegerSqrt
