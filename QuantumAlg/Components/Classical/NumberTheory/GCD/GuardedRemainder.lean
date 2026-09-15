/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.ScopedRemainder
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Stored-condition execution of the Euclidean loop body

The actual active bit selects either the scoped five-operation remainder
update or identity. The complete state equation reads that bit from each
incoming store block. The loop invariant is established internally by
initialization and preserved by this selected update.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private def remainderChoiceStep (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (store : Store ctx) : Store ctx ×
      (if value.toBool then scopedRemainder first second zero active else Circuit.id ctx).Path :=
  match value with
  | .bit false => (store, ())
  | .bit true => scopedRemainderStep first second zero active store

private theorem remainderChoice_execute (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (value : CShape.Value .bit) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (if value.toBool then scopedRemainder first second zero active else Circuit.id ctx).execute
      Reference state = state.mapClassical (fun entry =>
        ((remainderChoiceStep first second zero active value entry.1).1,
          (entry.2, (remainderChoiceStep first second zero active value entry.1).2))) := by
  cases value with
  | bit bit =>
      cases bit
      · simp only [CShape.Value.toBool, remainderChoiceStep]
        refine (Circuit.execute_id_mapClassical Reference state).trans ?_
        congr 1
        exact Subsingleton.elim _ _
      · simp only [CShape.Value.toBool, remainderChoiceStep]
        refine (gcdScopedRemainder_execute first second zero active Reference state).trans ?_
        congr 1

/-- The store and sigma path selected by the actual stored branch condition. -/
def guardedRemainderStep (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) : Store ctx × (guardedRemainder first second zero active).Path :=
  let value := store.read (cellRead active)
  let selected := remainderChoiceStep first second zero active value store
  (selected.1, ⟨value, selected.2⟩)

/-- The actual branch maps every complete input block to its actual store and selected path. -/
theorem gcdGuardedRemainder_execute (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (guardedRemainder first second zero active).execute Reference state =
      state.mapClassical (fun entry =>
        ((guardedRemainderStep first second zero active entry.1).1,
          (entry.2, (guardedRemainderStep first second zero active entry.1).2))) := by
  refine (Circuit.execute_branch_mapClassical (cellRead active) _
    (remainderChoiceStep first second zero active)
    (remainderChoice_execute first second zero active) Reference state).trans ?_
  congr 1

/-- The state update follows the actual bit, including an untouched inactive arm. -/
theorem gcdGuardedRemainder_step_store (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) :
    (guardedRemainderStep first second zero active store).1 =
      if (store.read (cellRead active)).toBool then
        (scopedRemainderStep first second zero active store).1 else store := by
  dsimp only [guardedRemainderStep]
  cases value : store.read (cellRead active) with
  | bit bit => cases bit <;> rfl

/-- Decode the two current word cells to the established pure Euclidean state. -/
def storedEuclidState (first second : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) : ClassicalAlgorithms.NumberTheory.Euclid.State :=
  decodeEuclidState (store.read (cellRead first)) (store.read (cellRead second))

/-- Internal initialization invariant: an actual zero word and its actual nonzero branch bit. -/
def storedEuclidReady (first : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (store : Store ctx) : Prop :=
  (store.read zero).toNat = 0 ∧
    (store.read (cellRead active)).toBool = decide ((store.read (cellRead first)).toNat ≠ 0)

/-- The selected body preserves initialization and realizes the terminating Euclidean step. -/
theorem gcdGuardedRemainder_store_transition (first second : CWriteRef ctx (.unsignedWord width))
    (zero : CInputRef ctx (.unsignedWord width)) (active : CWriteRef ctx .bit)
    (firstSecond : first.key ≠ second.key)
    (activeFirst : active.key ≠ first.key) (activeSecond : active.key ≠ second.key)
    (firstZero : first.key ∉ zero.storageKeys) (secondZero : second.key ∉ zero.storageKeys)
    (activeZero : active.key ∉ zero.storageKeys) (store : Store ctx)
    (ready : storedEuclidReady first zero active store) :
    let final := (guardedRemainderStep first second zero active store).1
    storedEuclidReady first zero active final ∧
      storedEuclidState first second final =
        if (storedEuclidState first second store).first = 0 then
          storedEuclidState first second store else
          ClassicalAlgorithms.NumberTheory.Euclid.step
            (storedEuclidState first second store) := by
  dsimp only
  rw [gcdGuardedRemainder_step_store]
  by_cases selected : (store.read (cellRead active)).toBool = true
  · rw [if_pos selected]
    have nonzero : (store.read (cellRead first)).toNat ≠ 0 :=
      of_decide_eq_true (ready.2.symm.trans selected)
    have nonzeroState : (storedEuclidState first second store).first ≠ 0 := nonzero
    rw [if_neg nonzeroState]
    have actual := gcdScopedRemainder_store_values first second zero active
      firstSecond activeFirst activeSecond firstZero secondZero activeZero store
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (congrArg CShape.Value.toNat actual.2.2.2).trans ready.1
    · rw [actual.2.2.1, actual.1, ready.1]
    · unfold storedEuclidState decodeEuclidState
        ClassicalAlgorithms.NumberTheory.Euclid.step
      rw [actual.1, actual.2.1]
  · rw [if_neg selected]
    have finished : (store.read (cellRead first)).toNat = 0 := by
      by_contra nonzero
      apply selected
      rw [ready.2]
      exact decide_eq_true nonzero
    have finishedState : (storedEuclidState first second store).first = 0 := finished
    rw [if_pos finishedState]
    exact ⟨ready, rfl⟩

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
