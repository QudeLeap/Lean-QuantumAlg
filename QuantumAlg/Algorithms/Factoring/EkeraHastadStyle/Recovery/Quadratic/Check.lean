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

/-- Actual range writes followed by actual remainder and conjunction writes. -/
def storeStep (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  Divisibility.storeStep refs.divisor (FactorRange.storeStep (rangeRefs refs) store)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Run all range and remainder instructions before using the resulting validity decision. -/
def code (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (FactorRange.code (model := model) (rangeRefs refs))
    (Divisibility.code (model := model) refs.divisor)

/-- Actual range outputs followed by actual remainder and predicate outputs. -/
def step (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (code (model := model) refs).Path :=
  let range := FactorRange.executionStep (model := model) (rangeRefs refs) store
  let divisor := Divisibility.step (model := model) refs.divisor range.1
  (divisor.1, (range.2, divisor.2))

/-- Full actual execution preserves all incoming quantum-reference blocks and the six true paths. -/
lemma nativeQuadratic_check_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code (model := model) refs).execute environment
      Reference state = state.mapClassical (fun entry =>
      let actual := step (model := model) refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [code, Circuit.execute_seq, FactorRange.code_execute,
    Divisibility.nativeQuadratic_divisibility_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.Check
