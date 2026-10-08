/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Offset.Loading.Layout

/-!
# Actual original three-coordinate offset loading
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeArithmetic (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Original second and third signed coordinate loaders use their supplied offset cells. -/
def suffixInto (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (ClassicalRoutines.ConstantWord.Signed.into offset.2.1 refs.offset.second)
    (ClassicalRoutines.ConstantWord.Signed.into offset.2.2 refs.offset.third)

/-- Complete actual stores and paths of the second and third initialized coordinate loops. -/
def suffixStep (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (suffixInto offset refs).Path :=
  let second := ClassicalRoutines.ConstantWord.Signed.step offset.2.1 refs.offset.second store
  let third := ClassicalRoutines.ConstantWord.Signed.step offset.2.2 refs.offset.third second.1
  (third.1, (second.2, third.2))

/-- All three original signed loading loops execute in their original coordinate order. -/
def setOffsetInto (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width) :
    Circuit model ctx ctx :=
  .seq (ClassicalRoutines.ConstantWord.Signed.into offset.1 refs.offset.first)
    (suffixInto offset refs)

/-- Actual complete three-coordinate store and the full native execution path. -/
def setOffsetStep (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (store : Store ctx) :
    Store ctx × (setOffsetInto offset refs).Path :=
  let first := ClassicalRoutines.ConstantWord.Signed.step offset.1 refs.offset.first store
  let suffix := suffixStep offset refs first.1
  (suffix.1, (first.2, suffix.2))

/-- Actual suffix loading preserves all incoming state blocks and chronological histories. -/
theorem suffixInto_execute (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (suffixInto offset refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := suffixStep offset refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (ClassicalRoutines.ConstantWord.Signed.into offset.2.1 refs.offset.second)
    (ClassicalRoutines.ConstantWord.Signed.into offset.2.2 refs.offset.third)
    (fun before =>
      let actual := ClassicalRoutines.ConstantWord.Signed.step offset.2.1
        refs.offset.second before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := ClassicalRoutines.ConstantWord.Signed.step offset.2.2
        refs.offset.third before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      ClassicalRoutines.ConstantWord.Signed.into_execute offset.2.1
        refs.offset.second reference current)
    (fun reference _history _ current =>
      ClassicalRoutines.ConstantWord.Signed.into_execute offset.2.2
        refs.offset.third reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual complete offset loading retains every original history and reference correlation. -/
theorem setOffsetInto_execute (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (setOffsetInto offset refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := setOffsetStep offset refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (ClassicalRoutines.ConstantWord.Signed.into offset.1 refs.offset.first) (suffixInto offset refs)
    (fun before =>
      let actual := ClassicalRoutines.ConstantWord.Signed.step offset.1
        refs.offset.first before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := suffixStep offset refs before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      ClassicalRoutines.ConstantWord.Signed.into_execute offset.1 refs.offset.first
        reference current)
    (fun reference _history _ current => suffixInto_execute offset refs reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

omit [BitWord.Selected model] in
/-- Different original offset coordinates have distinct actual write identities. -/
theorem mutable_avoids (refs : Refs ctx width) (separation : Separation refs)
    (saved written : MutableCell) (different : saved ≠ written) :
    (mutableRef refs written).key ∉ (writeInput (mutableRef refs saved)).storageKeys := by
  change mutableKey refs written ∉ [mutableKey refs saved]
  simp only [List.mem_singleton]
  intro equal
  exact different (separation.mutableInjective equal.symm)

/-- Reads outside the three original offset destinations form the complete caller frame. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ cell, mutableKey refs cell ∉ other.storageKeys) → after.read other = before.read other

/-- Every actual offset write preserves caller reads outside the original three-cell footprint. -/
theorem setOffsetInto_callerFrame (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (store : Store ctx) : CallerFrame refs store (setOffsetStep offset refs store).1 := by
  intro shape other avoids
  change (ClassicalRoutines.ConstantWord.Signed.step offset.2.2 refs.offset.third
    (ClassicalRoutines.ConstantWord.Signed.step offset.2.1 refs.offset.second
      (ClassicalRoutines.ConstantWord.Signed.step offset.1 refs.offset.first store).1).1).1.read
        other = _
  rw [ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.2.2 refs.offset.third _ other
      (avoids .third),
    ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.2.1 refs.offset.second _ other
      (avoids .second),
    ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.1 refs.offset.first _ other
      (avoids .first)]

/-- Actual raw offset output and all retained caller reads, with arbitrary initial offset cells. -/
structure Outcome (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (before after : Store ctx) : Prop where
  offset : LatticeArithmetic.PointRawRepresents after refs.offset offset
  callerFrame : CallerFrame refs before after

/-- The actual initialized signed loops materialize the original three integer coordinates. -/
theorem setOffsetInto_correct (offset : NumberTheory.IntegerPoint3) (refs : Refs ctx width)
    (separation : Separation refs) (store : Store ctx) :
    Outcome offset refs store (setOffsetStep offset refs store).1 := by
  refine ⟨⟨?_, ?_, ?_⟩, setOffsetInto_callerFrame offset refs store⟩
  · change RawSignedRepresents
      ((ClassicalRoutines.ConstantWord.Signed.step offset.2.2 refs.offset.third
        (ClassicalRoutines.ConstantWord.Signed.step offset.2.1 refs.offset.second
          (ClassicalRoutines.ConstantWord.Signed.step offset.1 refs.offset.first store).1).1).1.read
            (writeInput refs.offset.first)) offset.1
    rw [ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.2.2 refs.offset.third _
        (writeInput refs.offset.first)
        (mutable_avoids refs separation .first .third (by decide)),
      ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.2.1 refs.offset.second _
        (writeInput refs.offset.first)
        (mutable_avoids refs separation .first .second (by decide))]
    exact ClassicalRoutines.ConstantWord.Signed.into_correct _ _ _
  · change RawSignedRepresents
      ((ClassicalRoutines.ConstantWord.Signed.step offset.2.2 refs.offset.third
        (ClassicalRoutines.ConstantWord.Signed.step offset.2.1 refs.offset.second
          (ClassicalRoutines.ConstantWord.Signed.step offset.1 refs.offset.first store).1).1).1.read
            (writeInput refs.offset.second)) offset.2.1
    rw [ClassicalRoutines.ConstantWord.Signed.into_callerFrame offset.2.2 refs.offset.third _
      (writeInput refs.offset.second)
      (mutable_avoids refs separation .second .third (by decide))]
    exact ClassicalRoutines.ConstantWord.Signed.into_correct _ _ _
  · exact ClassicalRoutines.ConstantWord.Signed.into_correct _ _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeOffsetMaterializer
