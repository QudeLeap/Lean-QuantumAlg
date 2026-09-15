/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Layout
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual division followed by comparison of its stored remainder
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {numeratorWidth divisorWidth : Nat}

/-- The original native division reads both input words before writing its pair. -/
def divideOp (refs : Refs ctx numeratorWidth divisorWidth) :=
  ClassicalOp.divRem numeratorWidth divisorWidth ctx
    (.product refs.numerator refs.divisor) refs.division

/-- Native equality compares the real stored remainder with the supplied zero input. -/
def checkOp (refs : Refs ctx numeratorWidth divisorWidth) :=
  ClassicalOp.wordBinary .equal divisorWidth ctx
    (.product (remainderInput refs) refs.zero) refs.accepted

/-- Actual native division followed by the stored-remainder comparison. -/
def into (refs : Refs ctx numeratorWidth divisorWidth) : Circuit ctx ctx :=
  .seq (.classical (divideOp refs)) (.classical (checkOp refs))

/-- Complete actual store and chronological pair of native instruction paths. -/
def step (refs : Refs ctx numeratorWidth divisorWidth) (store : Store ctx) :
    Store ctx × (into refs).Path :=
  ((store.applyOp (divideOp refs)).applyOp (checkOp refs), ((), ()))

/-- The actual two-instruction circuit executes its full store and path record. -/
theorem into_execute (refs : Refs ctx numeratorWidth divisorWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) := by
  simp only [into, step, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatModCheck
