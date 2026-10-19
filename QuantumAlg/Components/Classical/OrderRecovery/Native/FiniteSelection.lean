/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.SlotState
import all QuantumAlg.Util.Classical.OrderRecovery

/-!
# Actual finite recovery selects the original source candidate

Induction follows the existing activity-gated store update. Every active
slot consumes one genuine candidate; acceptance freezes all remaining slots,
and a zero divisor has an empty source suffix. The result is exactly the
original finite source scan's selection, with no substituted outcome law or
second execution engine.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.OrderRecovery

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth phaseBits : Nat}

/-- Mathematical observation of the actual accepted latch and actual selected word. -/
def observedCandidate (cells : ScanCells ctx modulusWidth (phaseBits + 1))
    (store : Store ctx) : Option Nat :=
  if (store.read (cellRead cells.accepted)).toBool then
    some (store.read (cellRead cells.selected)).toNat
  else none

/-- An actual false accepted latch denotes no selected candidate. -/
lemma nativeScan_observed_pending
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx)
    (cursor : EuclideanContinuantCursor) (pending : PendingCursorReads cells store cursor) :
    observedCandidate cells store = none := by
  unfold observedCandidate
  rw [pending.accepted]
  rfl

/-- Actual selected-result reads denote precisely their represented candidate. -/
lemma nativeScan_observed_chosen
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (store : Store ctx) (candidate : Nat)
    (chosen : ChosenCursorReads cells store candidate) :
    observedCandidate cells store = some candidate := by
  unfold observedCandidate
  rw [chosen.accepted]
  exact congrArg some chosen.selected

/-- The actual fixed-fuel execution equals the original source selection on its genuine suffix. -/
lemma nativeScan_finite_source_selection {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (spec : Spec modulusWidth phaseBits) (input : Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (baseFree : ∀ key ∈ cells.writeKeys, key ∉ base.storageKeys)
    (fuel : Nat) (store : Store ctx) (cursor : EuclideanContinuantCursor)
    (pending : PendingCursorReads cells store cursor)
    (source : ScanSourceReads spec input base cells store)
    (remaining : cursor.actualCandidates ⊆ finiteCandidates (decodedIndex input))
    (bounded : cursor.actualCandidates.length ≤ fuel) :
    observedCandidate cells
      ((fun initial =>
          (scanSlotStep (model := model) spec.modulusSpec base cells initial).1)^[fuel] store) =
        (scanCandidates spec input cursor.actualCandidates).selection := by
  induction fuel generalizing store cursor with
  | zero =>
      have empty : cursor.actualCandidates = [] := List.eq_nil_of_length_eq_zero (by omega)
      change observedCandidate cells store = _
      rw [nativeScan_observed_pending cells store cursor pending, empty]
      rfl
  | succ fuel ih =>
      by_cases stopped : cursor.denominator = 0
      · have sourceInactive : cursor.active = false :=
          Bool.eq_false_iff.mpr (fun active =>
            ((EuclideanContinuantCursor.active_eq_true_iff cursor).mp active) stopped)
        have actualInactive := pending.active.trans (congrArg CShape.Value.bit sourceInactive)
        rw [nativeScan_iterate_of_inactive spec.modulusSpec base cells store actualInactive,
          nativeScan_observed_pending cells store cursor pending,
          EuclideanContinuantCursor.actualCandidates_eq_nil_of_inactive cursor stopped]
        rfl
      · have fits := dyadicCursor_candidate_fits_of_remaining (decodedIndex input) cursor
          remaining stopped
        have decision := nativeScan_slot_source_decision (model := model)
          spec input base cells separated baseFree
          store cursor pending source stopped fits
        have nextSource := nativeScan_slot_source_reads (model := model)
          spec input base cells separated baseFree
          store source
        have path := EuclideanContinuantCursor.actualCandidates_cons_of_active cursor stopped
        rw [Function.iterate_succ_apply]
        by_cases accepted : validateCandidate spec input cursor.candidate.denominator = true
        · rw [if_pos accepted] at decision
          have frozen := nativeScan_chosen_frozen (model := model)
            spec.modulusSpec base cells
            (scanSlotStep (model := model) spec.modulusSpec base cells store).1
            cursor.candidate.denominator
            decision fuel
          calc
            observedCandidate cells
                ((fun initial =>
                  (scanSlotStep (model := model) spec.modulusSpec base cells initial).1)^[fuel]
                  (scanSlotStep (model := model) spec.modulusSpec base cells store).1) =
                some cursor.candidate.denominator := nativeScan_observed_chosen cells _ _ frozen
            _ = (scanCandidates spec input cursor.actualCandidates).selection := by
              rw [path]
              simp only [scanCandidates, accepted, if_pos]
        · rw [if_neg accepted] at decision
          have nextRemaining :
              cursor.advance.actualCandidates ⊆ finiteCandidates (decodedIndex input) := by
            intro candidate member
            exact remaining (euclideanCursor_advance_candidates_subset cursor stopped member)
          have nextBound : cursor.advance.actualCandidates.length ≤ fuel := by
            rw [path, List.length_cons] at bounded
            exact Nat.le_of_succ_le_succ bounded
          calc
            observedCandidate cells
                ((fun initial =>
                  (scanSlotStep (model := model) spec.modulusSpec base cells initial).1)^[fuel]
                  (scanSlotStep (model := model) spec.modulusSpec base cells store).1) =
                (scanCandidates spec input cursor.advance.actualCandidates).selection :=
              ih _ _ decision nextSource nextRemaining nextBound
            _ = (scanCandidates spec input cursor.actualCandidates).selection := by
              rw [path]
              simp only [scanCandidates, if_neg accepted]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
