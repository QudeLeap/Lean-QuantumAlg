/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Basis.RowLoading.Correctness

/-!
# Actual original shared candidate constants

The supplied zero cell is cleared once. The original power-of-two loader
self-initializes the upper-bound cell, with no redundant external clear.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateConstants

open Execution
open ClassicalRoutines.NumberTheory.SignedWord
open LatticeLoading (writeInput)

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned cells holding zero and the strict exponent upper bound. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (width : Nat) where
  /-- Writable cell for the zero value. -/
  zero : CWriteRef ctx (.unsignedWord width)
  zeroRole : zero.toCStorageRef.role = .workspace
  /-- Writable cell for the upper bound value. -/
  upperBound : CWriteRef ctx (.unsignedWord width)
  upperBoundRole : upperBound.toCStorageRef.role = .workspace

/-- The two shared constant cells are distinct. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}
    (refs : Refs ctx width) : Prop where
  zeroAvoidsUpper :
    refs.upperBound.key ∉ (writeInput refs.zero).storageKeys

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Clear the original zero cell, then self-initialize and load the original upper bound. -/
def loadInto (m : Nat) (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model)
      (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))
    (ClassicalRoutines.Word.PowerOfTwo.into m refs.upperBound)

/-- The actual zero initialization and upper-bound stores with their full chronological paths. -/
def loadStep (m : Nat) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (loadInto m refs).Path :=
  let cleared := BitWord.instructionStep (execution := model)
    (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero) store
  let upper := ClassicalRoutines.Word.PowerOfTwo.step m refs.upperBound
    cleared.1
  (upper.1, (cleared.2, upper.2))

/-- The complete actual constant initializer retains all original execution-state blocks. -/
lemma loadInto_execute (m : Nat) (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadInto m refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := loadStep m refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment)
    (BitWord.instruction (execution := model)
      (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))
    (ClassicalRoutines.Word.PowerOfTwo.into m refs.upperBound)
    (fun before =>
      let actual := BitWord.instructionStep (execution := model)
        (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero) before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := ClassicalRoutines.Word.PowerOfTwo.step m refs.upperBound before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => BitWord.bitWord_instruction_execute
      (environment := environment) _ current)
    (fun reference _history _ current =>
      ClassicalRoutines.Word.PowerOfTwo.into_execute m refs.upperBound reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Every actual read outside the two original constant destinations remains unchanged. -/
def CallerFrame (refs : Refs ctx width) (before after : Store ctx) : Prop :=
  ∀ {shape : CShape} (other : CInputRef ctx shape),
    refs.zero.key ∉ other.storageKeys → refs.upperBound.key ∉ other.storageKeys →
      after.read other = before.read other

/-- Both actual initialization phases preserve every read outside the original two cells. -/
lemma loadInto_callerFrame (m : Nat) (refs : Refs ctx width) (store : Store ctx) :
    CallerFrame refs store (loadStep m refs store).1 := by
  intro shape other zero upper
  change (ClassicalRoutines.Word.PowerOfTwo.step m refs.upperBound
    (store.applyOp (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))).1.read other = _
  rw [ClassicalRoutines.Word.PowerOfTwo.into_callerFrame m refs.upperBound _ other upper,
    Store.read_applyOp_of_not_mem_storageKeys _ _ _ zero]

/-- Exact original raw constants and every retained caller read of actual initialization. -/
structure Outcome (m : Nat) (refs : Refs ctx width) (before after : Store ctx) : Prop where
  zero : RawSignedRepresents (after.read (writeInput refs.zero)) 0
  upperBound : RawSignedRepresents (after.read (writeInput refs.upperBound)) ((2 ^ m : Nat) : Int)
  callerFrame : CallerFrame refs before after

/-- Actual native initialization materializes both original constants from arbitrary storage. -/
lemma loadInto_correct (m : Nat) (refs : Refs ctx width) (separation : Separation refs)
    (store : Store ctx) : Outcome m refs store (loadStep m refs store).1 := by
  refine ⟨?_, ?_, loadInto_callerFrame m refs store⟩
  · change RawSignedRepresents ((ClassicalRoutines.Word.PowerOfTwo.step m refs.upperBound
      (store.applyOp (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))).1.read
        (writeInput refs.zero)) 0
    rw [ClassicalRoutines.Word.PowerOfTwo.into_callerFrame m refs.upperBound _
      (writeInput refs.zero) separation.zeroAvoidsUpper]
    change Int.ModEq _
      ((((store.applyOp (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero)).read
        (writeInput refs.zero)).toNat : Nat) : Int) 0
    rw [ClassicalRoutines.Word.PowerOfTwo.clear_read]
    rfl
  · change RawSignedRepresents ((LatticeLoading.powerStep m refs.upperBound
      (store.applyOp (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))).1.read
        (writeInput refs.upperBound)) ((2 ^ m : Nat) : Int)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      LatticeLoading.loadPowerOfTwoInto_represents m refs.upperBound
        (store.applyOp (ClassicalRoutines.Word.PowerOfTwo.clearOp refs.zero))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateConstants
