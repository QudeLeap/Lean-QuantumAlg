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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual signed normalization reads the candidate and writes only its sign and magnitude. -/
def normalizeInto (refs : Refs ctx width) : Circuit ctx ctx :=
  normalizeMagnitude (candidateInput refs) refs.negative refs.magnitude

/-- Actual complete normalized store and its selected native branch. -/
def normalizeStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (normalizeInto refs).Path :=
  normalizationStep (candidateInput refs) refs.negative refs.magnitude store

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
def suffixInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (.classical (copyOp refs))
    (.seq (.classical (equalOp refs))
      (.seq (.classical (positiveOp refs))
        (.seq (.classical (belowOp refs))
          (.seq (.classical (nonnegativeOp refs))
            (.seq (.classical (rangeOp refs)) (.classical (acceptedOp refs)))))))

/-- The actual seven chronological native updates after normalization. -/
def suffixStore (refs : Refs ctx width) (store : Store ctx) : Store ctx :=
  ((((((store.applyOp (copyOp refs)).applyOp (equalOp refs)).applyOp (positiveOp refs)).applyOp
    (belowOp refs)).applyOp (nonnegativeOp refs)).applyOp (rangeOp refs)).applyOp (acceptedOp refs)

/-- Complete actual suffix store and all seven instruction paths. -/
def suffixStep (refs : Refs ctx width) (store : Store ctx) : Store ctx × (suffixInto refs).Path :=
  (suffixStore refs store, ((), ((), ((), ((), ((), ((), ())))))))

/-- Direct actual sign extraction and magnitude selection precede the original range checks. -/
def candidateExponentInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .seq (normalizeInto refs) (suffixInto refs)

/-- Actual complete exponent store and the normalization branch followed by every range check. -/
def exponentStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (candidateExponentInto refs).Path :=
  let normalized := normalizeStep refs store
  let suffix := suffixStep refs normalized.1
  (suffix.1, (normalized.2, suffix.2))

/-- The actual seven-instruction suffix retains all incoming histories and reference blocks. -/
theorem suffixInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (suffixInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((suffixStep refs entry.1).1, (entry.2, (suffixStep refs entry.1).2))) := by
  simp only [suffixInto, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The complete actual classifier executes its real sign-selected magnitude branch. -/
theorem candidateExponentInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (candidateExponentInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((exponentStep refs entry.1).1, (entry.2, (exponentStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (normalizeInto refs) (suffixInto refs)
    (normalizeStep refs) (suffixStep refs)
    (normalizeMagnitude_execute (candidateInput refs) refs.negative refs.magnitude)
    (suffixInto_execute refs) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
