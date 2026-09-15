/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Initialize.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.Sqrt.Rounds.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Record

/-!
# Actual initialization, finite refinement and caller-visible square-root copy
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt

open Execution
open IntegerSqrt (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {inputWidth : Nat}

/-- Native copy from the final lower endpoint into the caller-visible output. -/
def finishOp (refs : Refs ctx inputWidth) :=
  ClassicalOp.wordUnary .copy (workWidth inputWidth) ctx
    (writeInput refs.round.root) refs.output

/-- The final actual caller-output write. -/
def finishInto (refs : Refs ctx inputWidth) : Circuit ctx ctx := .classical (finishOp refs)

/-- Actual output-write store and single native path. -/
def finishStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (finishInto refs).Path := (store.applyOp (finishOp refs), ())

private theorem finishInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (finishInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((finishStep refs entry.1).1, (entry.2, (finishStep refs entry.1).2))) := by
  refine (Circuit.execute_classical_mapClassical (finishOp refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- The exact finite refinement followed by the actual final output copy. -/
def refineInto (refs : Refs ctx inputWidth) : Circuit ctx ctx :=
  .seq (roundsInto refs inputWidth) (finishInto refs)

/-- Chronological record of refinement and the final caller-output write. -/
def refineStep (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (refineInto refs).Path :=
  Circuit.sequenceRecord (roundsInto refs inputWidth) (finishInto refs)
    (roundsStep refs inputWidth) (finishStep refs) store

private theorem refineInto_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (refineInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((refineStep refs entry.1).1, (entry.2, (refineStep refs entry.1).2))) :=
  Circuit.execute_sequenceRecord (roundsInto refs inputWidth) (finishInto refs)
    (roundsStep refs inputWidth) (finishStep refs) (roundsInto_execute refs inputWidth)
    (finishInto_execute refs) Reference state

/-- Complete actual natural-square-root driver on the original caller-supplied cells. -/
def into (refs : Refs ctx inputWidth) : Circuit ctx ctx :=
  .seq (initializeInto refs) (refineInto refs)

/-- Complete actual driver record, including all initialization and branch-dependent paths. -/
def step (refs : Refs ctx inputWidth) (store : Store ctx) :
    Store ctx × (into refs).Path :=
  Circuit.sequenceRecord (initializeInto refs) (refineInto refs)
    (initializeStep refs) (refineStep refs) store

/-- The returned caller store is the actual copy after initialization and every refinement. -/
theorem step_store (refs : Refs ctx inputWidth) (store : Store ctx) :
    (step refs store).1 =
      (roundsStep refs inputWidth (initializeStep refs store).1).1.applyOp (finishOp refs) := rfl

/-- The actual driver retains the full incoming classical history and quantum-reference state. -/
theorem into_execute (refs : Refs ctx inputWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into refs).execute Reference state = state.mapClassical (fun entry =>
      ((step refs entry.1).1, (entry.2, (step refs entry.1).2))) :=
  Circuit.execute_sequenceRecord (initializeInto refs) (refineInto refs)
    (initializeStep refs) (refineStep refs) (initializeInto_execute refs)
    (refineInto_execute refs) Reference state

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NatSqrt
