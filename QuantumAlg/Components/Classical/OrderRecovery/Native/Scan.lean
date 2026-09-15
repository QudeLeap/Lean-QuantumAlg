/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Cursor
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Validation

/-!
# Actual continued-fraction candidate visit and selection

The division pair is live during one active visit. Its quotient materializes
the candidate; its remainder remains available to the rejection branch. The
selection reads the actual final validation bit, and only its chosen update
contributes events. Allocation and the outer active test belong to the lexical
scan assembly, so no inactive slot performs a synthetic division.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

/-- Actual cursor, result latches and modular-validation cells of one recovery scan. -/
structure ScanCells (ctx : RuntimeCtx kind) (modulusWidth candidateWidth : Nat) where
  cursor : CursorCells ctx candidateWidth
  selected : CWriteRef ctx (.unsignedWord candidateWidth)
  accepted : CWriteRef ctx .bit
  zero : CInputRef ctx (.unsignedWord candidateWidth)
  one : CInputRef ctx (.unsignedWord modulusWidth)
  power : CWriteRef ctx (.unsignedWord modulusWidth)
  positive : CWriteRef ctx .bit
  valid : CWriteRef ctx .bit

/-- The two actual update bodies selected by the stored validation result. -/
def selectionChoice (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth))
    (value : CShape.Value .bit) : Circuit ctx ctx :=
  if value.toBool then
    acceptCursor (cellRead cells.cursor.candidate) (cellRead cells.valid)
      cells.selected cells.accepted cells.cursor.active
  else
    advanceCursor cells.cursor remainder cells.zero

/-- The concrete store and branch-local path of the chosen update. -/
def selectionChoiceStep (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth))
    (value : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (selectionChoice cells remainder value).Path :=
  match value with
  | .bit false =>
      (advanceCursorStore cells.cursor remainder cells.zero store, ((), ((), ((), ((), ())))))
  | .bit true =>
      (acceptCursorStore (cellRead cells.cursor.candidate) (cellRead cells.valid)
        cells.selected cells.accepted cells.cursor.active store, ((), ((), ())))

private theorem selectionChoice_execute (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth))
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (selectionChoice cells remainder value).execute Reference state =
      state.mapClassical (fun entry =>
        ((selectionChoiceStep cells remainder value entry.1).1,
          (entry.2, (selectionChoiceStep cells remainder value entry.1).2))) := by
  cases value with
  | bit value =>
      cases value
      · refine (nativeCursor_advance_execute cells.cursor remainder cells.zero
          Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · refine (nativeCursor_accept_execute (cellRead cells.cursor.candidate) (cellRead cells.valid)
          cells.selected cells.accepted cells.cursor.active Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _

/-- The actual validation-bit read chooses the acceptance or Euclidean-advance body. -/
def selectCandidate (cells : ScanCells ctx modulusWidth candidateWidth)
    (remainder : CInputRef ctx (.unsignedWord candidateWidth)) : Circuit ctx ctx :=
  .branch (cellRead cells.valid) (selectionChoice cells remainder)

/-- The full active visit uses one stored division pair and its real quotient and remainder. -/
def visitWithDivision (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (division : CWriteRef ctx
      (.product (.unsignedWord candidateWidth) (.unsignedWord candidateWidth))) : Circuit ctx ctx :=
  .seq (candidatePrefix (cellRead cells.cursor.numerator) (cellRead cells.cursor.denominator)
    (cellRead cells.cursor.previous) (cellRead cells.cursor.older) division cells.cursor.candidate)
    (.seq (validate spec base (cellRead cells.cursor.candidate) cells.zero cells.one
      cells.power cells.positive cells.valid)
      (selectCandidate cells (.second (cellRead division))))

/-- The actual prefix, validation and selected branch determine a complete visit record. -/
def visitWithDivisionStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (division : CWriteRef ctx
      (.product (.unsignedWord candidateWidth) (.unsignedWord candidateWidth)))
    (store : Store ctx) :
    Store ctx × (visitWithDivision spec base cells division).Path :=
  let materialized := candidatePrefixStep (cellRead cells.cursor.numerator)
    (cellRead cells.cursor.denominator) (cellRead cells.cursor.previous)
    (cellRead cells.cursor.older) division cells.cursor.candidate store
  let validated := validateStep spec base (cellRead cells.cursor.candidate) cells.zero cells.one
    cells.power cells.positive cells.valid materialized.1
  let value := validated.1.read (cellRead cells.valid)
  let selected := selectionChoiceStep cells (.second (cellRead division)) value validated.1
  (selected.1, (materialized.2, (validated.2, ⟨value, selected.2⟩)))

/-- The actual visit composes its two deterministic prefixes and same-store classical selection. -/
theorem nativeScan_visitWithDivision_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth)
    (division : CWriteRef ctx
      (.product (.unsignedWord candidateWidth) (.unsignedWord candidateWidth)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (visitWithDivision spec base cells division).execute Reference state =
      state.mapClassical (fun entry =>
        ((visitWithDivisionStep spec base cells division entry.1).1,
          (entry.2, (visitWithDivisionStep spec base cells division entry.1).2))) := by
  have selectedExecute {H : Type} [Fintype H] (reference : Register)
      (initial : State ctx reference H) :
      (selectCandidate cells (.second (cellRead division))).execute reference initial =
        initial.mapClassical (fun entry =>
          ((selectionChoiceStep cells (.second (cellRead division))
            (entry.1.read (cellRead cells.valid)) entry.1).1,
            (entry.2, ⟨entry.1.read (cellRead cells.valid),
              (selectionChoiceStep cells (.second (cellRead division))
                (entry.1.read (cellRead cells.valid)) entry.1).2⟩))) :=
    Circuit.execute_branch_mapClassical (cellRead cells.valid) _
      (selectionChoiceStep cells (.second (cellRead division)))
      (selectionChoice_execute cells (.second (cellRead division))) reference initial
  simp only [visitWithDivision, Circuit.execute_seq, nativeCandidatePrefix_execute,
    nativeValidation_execute, selectedExecute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
