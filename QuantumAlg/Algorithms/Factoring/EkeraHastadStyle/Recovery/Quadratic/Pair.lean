/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection

/-!
# Actual complete checks followed by the original left-priority selection

Both candidates undergo all six range and divisibility instructions, including
when an earlier result is already accepted. Only then do the two actual
first-accepted selectors consume the computed validity cells in source order.
The same structural references supply checked words to those possible copies.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The two actual checker interfaces and the shared real first-factor latches. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Check for the lower quadratic candidate. -/
  first : Check.Refs ctx width
  /-- Check for the upper quadratic candidate. -/
  second : Check.Refs ctx width
  /-- Persistent latches shared with preceding candidate pairs. -/
  selection : FirstAccepted.Refs ctx width

/-- The selector reads the same candidate word and actual final checker bit. -/
def selectedInputs (checked : Check.Refs ctx width) : FirstAccepted.Inputs ctx width where
  eligible := .storage checked.divisor.valid.toCStorageRef
  candidate := checked.divisor.candidate

/-- Both complete checks run before any first-factor latch is conditionally updated. -/
def code (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (Check.code refs.first)
    (.seq (Check.code refs.second)
      (Selection.code (selectedInputs refs.first) (selectedInputs refs.second) refs.selection))

/-- All twelve actual writes before left-priority selection. -/
def checkedStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  Check.storeStep refs.second (Check.storeStep refs.first store)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual complete store and chronological paths of checking and selection. -/
def step (refs : Refs ctx width) (store : Store ctx) : Store ctx × (code refs).Path :=
  let selected := Selection.step (selectedInputs refs.first) (selectedInputs refs.second)
    refs.selection (checkedStore refs store)
  (selected.1, ((((), ((), ())), ((), ((), ()))),
    ((((), ((), ())), ((), ((), ()))), selected.2)))

/-- Complete actual pair execution preserves every incoming quantum-reference block. -/
theorem nativeQuadratic_pair_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  let selection := Selection.code (selectedInputs refs.first) (selectedInputs refs.second)
    refs.selection
  let selectStep := Selection.step (selectedInputs refs.first) (selectedInputs refs.second)
    refs.selection
  refine (Circuit.execute_seq_mapClassical (Check.code refs.first)
    (.seq (Check.code refs.second) selection)
    (fun store => (Check.storeStep refs.first store, (((), ((), ())), ((), ((), ())))))
    (fun store =>
      let selected := selectStep (Check.storeStep refs.second store)
      (selected.1, ((((), ((), ())), ((), ((), ()))), selected.2)))
    (fun reference {_} _ initial => by
      refine (Check.nativeQuadratic_check_execute refs.first reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (Circuit.execute_seq_mapClassical (Check.code refs.second) selection
        (fun store => (Check.storeStep refs.second store, (((), ((), ())), ((), ((), ())))))
        selectStep
        (fun reference {_} _ initial => by
          refine (Check.nativeQuadratic_check_execute refs.second reference initial).trans ?_
          congr 1
          exact Subsingleton.elim _ _)
        (fun reference {_} _ initial => by
          refine (Selection.nativeQuadratic_selection_execute
            (selectedInputs refs.first) (selectedInputs refs.second)
            refs.selection reference initial).trans ?_
          congr 1)
        reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (code refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry => ((step refs entry.1).1, (entry.2, (step refs entry.1).2))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Pair
