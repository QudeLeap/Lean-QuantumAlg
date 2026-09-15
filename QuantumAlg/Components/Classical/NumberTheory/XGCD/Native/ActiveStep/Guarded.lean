/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.ActiveStep.Scoped
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# The actual stored-condition extended-Euclidean update

The incoming activity bit selects the existing scoped body or identity.
The same selected record retains the real store, sigma path and every full
quantum-reference block. Signed ranges are needed only for an active step.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Initialization establishes a real zero word and an activity bit matching the first remainder. -/
def storedReady (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width)) (store : Store ctx) : Prop :=
  (store.read zero).toNat = 0 ∧
    (store.read (GCD.cellRead (activeCell cells))).toBool =
      decide ((storedState cells store).first ≠ 0)

private def activeChoiceRecord (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (scopedActive cells zero).Path)
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx ×
      (if value.toBool then scopedActive cells zero else Circuit.id ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => record store

private theorem activeChoice_execute (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (scopedActive cells zero).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (scopedActive cells zero).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2))))
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (if value.toBool then scopedActive cells zero else Circuit.id ctx).execute Reference state =
      state.mapClassical (fun entry =>
        ((activeChoiceRecord cells zero record value entry.1).1,
          (entry.2, (activeChoiceRecord cells zero record value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, activeChoiceRecord]
        refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, activeChoiceRecord]
        exact equation Reference state

/-- The selected record reads the actual incoming activity cell and retains its sigma path. -/
def guardedActiveRecord (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (scopedActive cells zero).Path)
    (store : Store ctx) : Store ctx × (guardedActive cells zero).Path :=
  let value := store.read (GCD.cellRead (activeCell cells))
  let selected := activeChoiceRecord cells zero record value store
  (selected.1, ⟨value, selected.2⟩)

/-- The actual branch has the same complete store and path record as its selected execution. -/
theorem xgcdNativeGuardedActive_execute (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (scopedActive cells zero).Path)
    (equation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference History),
      (scopedActive cells zero).execute Reference state = state.mapClassical (fun entry =>
        ((record entry.1).1, (entry.2, (record entry.1).2))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (guardedActive cells zero).execute Reference state = state.mapClassical (fun entry =>
      ((guardedActiveRecord cells zero record entry.1).1,
        (entry.2, (guardedActiveRecord cells zero record entry.1).2))) := by
  exact Circuit.execute_branch_mapClassical (GCD.cellRead (activeCell cells)) _
    (activeChoiceRecord cells zero record) (activeChoice_execute cells zero record equation)
    Reference state

/-- The returned store follows the real bit; the inactive arm retains the entire input store. -/
theorem xgcdNativeGuardedActive_record_store (cells : Cells ctx (stateShapes width))
    (zero : CInputRef ctx (.unsignedWord width))
    (record : Store ctx → Store ctx × (scopedActive cells zero).Path)
    (store : Store ctx) :
    (guardedActiveRecord cells zero record store).1 =
      if (store.read (GCD.cellRead (activeCell cells))).toBool then
        (record store).1 else store := by
  dsimp only [guardedActiveRecord]
  cases value : store.read (GCD.cellRead (activeCell cells)) with
  | bit bit => cases bit <;> rfl

/-- The actual selected record preserves readiness and realizes the original stopping rule. -/
theorem xgcdNativeGuardedActive_actualRecord
    (cells : Cells ctx (stateShapes width)) (distinct : cells.Distinct)
    (zero : CInputRef ctx (.unsignedWord width))
    (stateZero : ∀ index : Fin 7, stateKey cells index ∉ zero.storageKeys) :
    ∃ record : Store ctx → Store ctx × (guardedActive cells zero).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference History),
        (guardedActive cells zero).execute Reference state =
          state.mapClassical (fun entry =>
            ((record entry.1).1, (entry.2, (record entry.1).2)))) ∧
      ∀ before : Store ctx,
        (∀ {shape : CShape} (other : CInputRef ctx shape),
          (∀ index : Fin 7, stateKey cells index ∉ other.storageKeys) →
            ((record before).1).read other = before.read other) ∧
        (storedReady cells zero before →
          ((storedState cells before).first ≠ 0 →
            ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
              (PureXGCD.executionCoefficientWidth width)
              (PureXGCD.step (storedState cells before)).firstLeftCoefficient ∧
            ClassicalAlgorithms.NumberTheory.XGCD.signedRepresentable
              (PureXGCD.executionCoefficientWidth width)
              (PureXGCD.step (storedState cells before)).firstRightCoefficient) →
          storedReady cells zero (record before).1 ∧
            storedState cells (record before).1 =
              if (storedState cells before).first = 0 then storedState cells before
              else PureXGCD.step (storedState cells before)) := by
  obtain ⟨scopedRecord, equation, correct⟩ :=
    xgcdNativeScopedActive_actualRecord (width := width) cells distinct zero stateZero
  refine ⟨guardedActiveRecord cells zero scopedRecord,
    xgcdNativeGuardedActive_execute cells zero scopedRecord equation, ?_⟩
  intro before
  constructor
  · intro shape other free
    rw [xgcdNativeGuardedActive_record_store]
    split
    · exact (correct before).1 other free
    · rfl
  · intro ready ranges
    rw [xgcdNativeGuardedActive_record_store]
    by_cases selected : (before.read (GCD.cellRead (activeCell cells))).toBool = true
    · rw [if_pos selected]
      have nonzero : (storedState cells before).first ≠ 0 :=
        of_decide_eq_true (ready.2.symm.trans selected)
      rw [if_neg nonzero]
      refine ⟨⟨?_, (correct before).2.2 ready.1⟩,
        (correct before).2.1 (ranges nonzero).1 (ranges nonzero).2⟩
      exact (congrArg CShape.Value.toNat ((correct before).1 zero stateZero)).trans ready.1
    · rw [if_neg selected]
      have finished : (storedState cells before).first = 0 := by
        by_contra nonzero
        exact selected (ready.2.trans (decide_eq_true nonzero))
      rw [if_pos finished]
      exact ⟨ready, rfl⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
