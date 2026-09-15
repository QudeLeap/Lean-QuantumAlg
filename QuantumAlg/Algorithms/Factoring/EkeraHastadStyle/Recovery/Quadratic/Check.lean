/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.FactorRange
import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Divisibility

/-!
# Complete actual range and divisibility check for one candidate

The unique shared range component performs both original unsigned comparisons.
The actual remainder and equality are then computed unconditionally, before
the stored result is conjoined with that range result. All six instructions
operate on the same real context; neither an arbitrary initial decision bit
nor a previous successful candidate suppresses this check.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Check

open Execution
open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual words and predicate cells shared by range and remainder instructions. -/
structure Refs (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Original modulus, candidate and zero read with the remainder, equality and validity cells. -/
  divisor : Divisibility.Refs ctx width
  /-- Real initialized word containing the strict lower endpoint. -/
  one : CInputRef ctx (.unsignedWord width)
  /-- Real second comparison cell used by the unique range component. -/
  upper : CWriteRef ctx .bit

/-- The unique shared range code receives the same actual modulus and candidate as division. -/
def rangeRefs (refs : Refs ctx width) : FactorRange.Refs ctx width where
  candidate := refs.divisor.candidate
  one := refs.one
  modulus := refs.divisor.modulus
  lower := refs.divisor.valid
  upper := refs.upper

/-- Run all range and remainder instructions before using the resulting validity decision. -/
def code (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (FactorRange.code (rangeRefs refs)) (Divisibility.code refs.divisor)

/-- Actual range writes followed by actual remainder and conjunction writes. -/
def storeStep (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  Divisibility.storeStep refs.divisor (FactorRange.storeStep (rangeRefs refs) store)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Full actual execution preserves all incoming quantum-reference blocks and the six true paths. -/
theorem nativeQuadratic_check_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (code refs).execute Reference state = state.mapClassical (fun entry =>
      (storeStep refs entry.1, (entry.2, (((), ((), ())), ((), ((), ())))))) := by
  refine (Circuit.execute_seq_mapClassical
    (FactorRange.code (rangeRefs refs)) (Divisibility.code refs.divisor)
    (fun store => (FactorRange.storeStep (rangeRefs refs) store, ((), ((), ()))))
    (fun store => (Divisibility.storeStep refs.divisor store, ((), ((), ()))))
    (fun reference {_} _ initial => by
      refine (FactorRange.code_execute (rangeRefs refs) reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    (fun reference {_} _ initial => by
      refine (Divisibility.nativeQuadratic_divisibility_execute
        refs.divisor reference initial).trans ?_
      congr 1
      exact Subsingleton.elim _ _)
    Reference state).trans ?_
  exact congrArg
    (fun equality : DecidableEq (Store ctx × (History × (code refs).Path)) =>
      @ExecutionState.mapClassical _ _ _ _ (Register.prod ctx.register Reference) equality state
        (fun entry =>
          (storeStep refs entry.1, (entry.2, (((), ((), ())), ((), ((), ())))))))
    (Subsingleton.elim _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Check
