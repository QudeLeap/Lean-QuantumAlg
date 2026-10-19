/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.NearestPlane.Third.Layout
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Classification.Normalization

/-!
# Actual stored-sign correction of the third numerator

The real denominator sign selects either two native in-place negation writes
or the identity. The actual branch result records the flag read from storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird

open ClassicalRoutines.NumberTheory.SignedWord
open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Reuse the native complement/increment arm, or leave the actual numerator unchanged. -/
def numeratorSignChoice {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit false => .id ctx
  | .bit true => magnitudeArm (writeInput refs.numerator) refs.numerator (.bit true)

/-- Actual writes of the chosen numerator-sign arm. -/
def numeratorSignArmStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (numeratorSignChoice refs flag).Path :=
  match flag with
  | .bit false => (store, ())
  | .bit true => magnitudeArmStep (writeInput refs.numerator) refs.numerator (.bit true) store

/-- The stored denominator sign selects the actual numerator correction. -/
def numeratorSignInto {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (writeInput refs.division.negative) (numeratorSignChoice refs)

/-- The actual selected numerator state and branch record. -/
def numeratorSignStep {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (numeratorSignInto refs).Path :=
  let selected := numeratorSignArmStep refs (store.read (writeInput refs.division.negative)) store
  (selected.1, ⟨store.read (writeInput refs.division.negative), selected.2⟩)

private lemma numeratorSignChoice_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (numeratorSignChoice refs flag).execute environment Reference state
      = state.mapClassical (fun entry =>
      let actual := numeratorSignArmStep refs flag entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  cases flag with
  | bit flag =>
    cases flag
    · refine (Circuit.execute_id_mapClassical (environment := environment) Reference state).trans ?_
      exact ExecutionState.executionState_mapClassical_congr _ rfl
    · simp only [numeratorSignChoice, numeratorSignArmStep, magnitudeArm, magnitudeArmStep,
        Circuit.execute_seq, BitWord.bitWord_instruction_execute, State.mapHistory,
        ExecutionState.executionState_mapClassical_comp, Function.comp_def]
      exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The complete actual branch preserves histories and quantum-reference blocks. -/
lemma numeratorSignInto_execute {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (numeratorSignInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := numeratorSignStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_branch_mapClassical
    (environment := environment) (writeInput refs.division.negative)
    (numeratorSignChoice refs)
    (fun flag before =>
      let actual := numeratorSignArmStep refs flag before.1
      ((actual.1, before.2), actual.2))
    (fun flag reference _history _ current =>
      numeratorSignChoice_execute refs flag reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual numerator correction changes only the existing numerator cell. -/
lemma numeratorSignInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : refs.numerator.key ∉ other.storageKeys) :
    (numeratorSignStep refs store).1.read other = store.read other := by
  unfold numeratorSignStep
  cases stored : store.read (writeInput refs.division.negative) with
  | bit flag =>
    cases flag
    · rfl
    · change (((store.applyOp (magnitudeComplementOp
        (writeInput refs.numerator) refs.numerator)).applyOp
          (magnitudeIncrementOp refs.numerator)).read other) = store.read other
      rw [Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids,
        Store.read_applyOp_of_not_mem_storageKeys _ _ _ avoids]

private lemma unary_read (opcode : Resource.WordUnaryOpcode) (store : Store ctx)
    (input : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (.unsignedWord width)) :
    (store.applyOp (.wordUnary opcode width ctx input output)).read (writeInput output) =
      opcode.eval width (store.read input) :=
  Store.read_applyOp_output store (.wordUnary opcode width ctx input output)

/-- The actual flag chooses the corresponding original integer numerator sign. -/
lemma numeratorSignInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (store : Store ctx) (value : Int)
    (rep : RawSignedRepresents (store.read (writeInput refs.numerator)) value) :
    RawSignedRepresents ((numeratorSignStep refs store).1.read (writeInput refs.numerator))
      (if (store.read (writeInput refs.division.negative)).toBool then -value else value) := by
  unfold numeratorSignStep
  cases stored : store.read (writeInput refs.division.negative) with
  | bit flag =>
    cases flag
    · exact rep
    · change RawSignedRepresents
        (((store.applyOp (magnitudeComplementOp
          (writeInput refs.numerator) refs.numerator)).applyOp
            (magnitudeIncrementOp refs.numerator)).read (writeInput refs.numerator)) (-value)
      unfold magnitudeIncrementOp magnitudeComplementOp
      rw [unary_read .increment, unary_read .complement]
      exact rawSignedWordRepresents_negate _ value rep

/-- The recorded actual flag determines the independent two-instruction or empty native trace. -/
lemma numeratorSignInto_events {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
    (numeratorSignInto refs).eventTrace path =
      if path.1.toBool then
        [.classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .complement width)),
          .classicalOperation (BitWord.selectedCoordinate (execution := model)
            (.wordUnary .increment width))] else [] := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · rfl
    · dsimp only [numeratorSignInto, numeratorSignChoice] at path ⊢
      change _ ++ _ = _
      rw [BitWord.bitWord_instruction_eventTrace,
        BitWord.bitWord_instruction_eventTrace]
      rfl

/-- At most two actual native operations correct the numerator sign. -/
lemma numeratorSignInto_eventCount_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width)
    (path : (numeratorSignInto refs).Path) :
    ((numeratorSignInto refs).eventTrace path).length ≤ 2 := by
  rw [numeratorSignInto_events]
  split <;> simp only [List.length_cons, List.length_nil] <;> decide

/-- The actual selected correction has unit-duration depth at most two. -/
lemma numeratorSignInto_depth_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
    (numeratorSignInto refs).depth (fun _ => 1) path ≤ 2 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · change 0 ≤ 2
      decide
    · change 2 ≤ 2
      exact le_rfl

/-- Both the identity and the two native writes jointly restore all borrowed correlations. -/
lemma numeratorSignInto_borrowedRestored {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (numeratorSignInto refs).BorrowedRestored Reference state
      ((numeratorSignInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment) _ _ Reference _ state
  intro flag history _ current
  cases flag with
  | bit flag =>
    cases flag
    · exact Circuit.borrowedRestored_id (environment := environment) current
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ current
        (Circuit.borrowedRestored_classical
          (environment := environment) _ _) (Circuit.borrowedRestored_classical (environment :=
          environment) _ _)

/-- Every actual correction instruction, including the idle arm, retains the caller context. -/
lemma numeratorSignInto_visited {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
    (numeratorSignInto refs).visitedContexts path =
      if path.1.toBool then [ctx, ctx] else [ctx] := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
