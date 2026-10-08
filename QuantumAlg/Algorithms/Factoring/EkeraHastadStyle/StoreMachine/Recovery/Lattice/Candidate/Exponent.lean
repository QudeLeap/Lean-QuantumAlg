/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Layout

/-!
# Actual candidate-exponent normalization and range checks
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Actual signed normalization reads the candidate and writes only its sign and magnitude. -/
def normalizeInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  normalizeMagnitude (model := model) (candidateInput refs) refs.negative refs.magnitude

/-- Actual complete normalized store and its selected native branch. -/
def normalizeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (normalizeInto refs).Path :=
  normalizationStep (model := model) (candidateInput refs) refs.negative refs.magnitude store

/-- Actual native copy for the original exponent consumer cell. -/
def copyOp (refs : Refs ctx width) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
  .wordUnary .copy width ctx (writeInput refs.magnitude) refs.exponent

/-- Actual equality against the supplied zero word. -/
def equalOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product (writeInput refs.magnitude) refs.zero) refs.positive

/-- Actual negation converts the stored zero test into a nonzero test. -/
def positiveOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (writeInput refs.positive) refs.positive

/-- Actual unsigned comparison against the supplied original upper-bound word. -/
def belowOp (refs : Refs ctx width) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .lessThan width ctx (.product (writeInput refs.magnitude) refs.upperBound)
    refs.belowUpper

/-- Actual stored-sign negation for the original nonnegative test. -/
def nonnegativeOp (refs : Refs ctx width) : ClassicalOp .bit .bit ctx ctx :=
  .bit .not ctx (writeInput refs.negative) refs.nonnegative

/-- The first actual conjunction combines nonzero magnitude with the strict upper bound. -/
def rangeOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (writeInput refs.positive) (writeInput refs.belowUpper)) refs.accepted

/-- The final actual conjunction requires the original candidate to be nonnegative. -/
def acceptedOp (refs : Refs ctx width) : ClassicalOp (.product .bit .bit) .bit ctx ctx :=
  .bit .and ctx (.product (writeInput refs.accepted) (writeInput refs.nonnegative)) refs.accepted

/-- The original seven native suffix instructions read the actual normalized cells and flags. -/
def suffixInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (copyOp refs))
    (.seq (BitWord.instruction (execution := model) (equalOp refs))
      (.seq (BitWord.instruction (execution := model) (positiveOp refs))
        (.seq (BitWord.instruction (execution := model) (belowOp refs))
          (.seq (BitWord.instruction (execution := model) (nonnegativeOp refs))
            (.seq (BitWord.instruction (execution := model) (rangeOp refs))
              (BitWord.instruction (execution := model) (acceptedOp refs)))))))

/-- The actual seven chronological native updates after normalization. -/
def suffixStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((((((store.applyOp (copyOp refs)).applyOp (equalOp refs)).applyOp (positiveOp refs)).applyOp
    (belowOp refs)).applyOp (nonnegativeOp refs)).applyOp (rangeOp refs)).applyOp (acceptedOp refs)

/-- Complete actual suffix store and all seven instruction paths. -/
def suffixStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (suffixInto refs).Path :=
  let copied := BitWord.instructionStep (execution := model) (copyOp refs) store
  let equalled := BitWord.instructionStep (execution := model) (equalOp refs) copied.1
  let positive := BitWord.instructionStep (execution := model) (positiveOp refs) equalled.1
  let below := BitWord.instructionStep (execution := model) (belowOp refs) positive.1
  let nonnegative := BitWord.instructionStep (execution := model) (nonnegativeOp refs) below.1
  let ranged := BitWord.instructionStep (execution := model) (rangeOp refs) nonnegative.1
  let accepted := BitWord.instructionStep (execution := model) (acceptedOp refs) ranged.1
  (accepted.1, (copied.2, (equalled.2, (positive.2, (below.2,
    (nonnegative.2, (ranged.2, accepted.2)))))))

/-- Direct actual sign extraction and magnitude selection precede the original range checks. -/
def candidateExponentInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (normalizeInto refs) (suffixInto refs)

/-- Actual complete exponent store and the normalization branch followed by every range check. -/
def exponentStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateExponentInto refs).Path :=
  let normalized := normalizeStep refs store
  let suffix := suffixStep refs normalized.1
  (suffix.1, (normalized.2, suffix.2))

/-- The actual seven-instruction suffix retains all incoming histories and reference blocks. -/
theorem suffixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (suffixInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := suffixStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  simp only [suffixInto, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete actual classifier executes its real sign-selected magnitude branch. -/
theorem candidateExponentInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateExponentInto refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := exponentStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (normalizeInto refs) (suffixInto refs)
    (fun before =>
      let actual := normalizeStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := suffixStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      normalizeMagnitude_execute (model := model) (candidateInput refs)
        refs.negative refs.magnitude reference current)
    (fun reference _history _ current => suffixInto_execute refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
