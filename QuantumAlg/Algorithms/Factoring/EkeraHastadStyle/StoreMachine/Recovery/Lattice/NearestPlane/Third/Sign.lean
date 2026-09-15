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
def numeratorSignChoice (refs : Refs ctx width) : CShape.Value .bit → Circuit ctx ctx
  | .bit false => .id ctx
  | .bit true => magnitudeArm (writeInput refs.numerator) refs.numerator (.bit true)

/-- Actual writes of the chosen numerator-sign arm. -/
def numeratorSignArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (numeratorSignChoice refs flag).Path :=
  match flag with
  | .bit false => (store, ())
  | .bit true => magnitudeArmStep (writeInput refs.numerator) refs.numerator (.bit true) store

/-- The stored denominator sign selects the actual numerator correction. -/
def numeratorSignInto (refs : Refs ctx width) : Circuit ctx ctx :=
  .branch (writeInput refs.division.negative) (numeratorSignChoice refs)

/-- The actual selected numerator state and branch record. -/
def numeratorSignStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (numeratorSignInto refs).Path :=
  let selected := numeratorSignArmStep refs (store.read (writeInput refs.division.negative)) store
  (selected.1, ⟨store.read (writeInput refs.division.negative), selected.2⟩)

private theorem numeratorSignChoice_execute (refs : Refs ctx width) (flag : CShape.Value .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (numeratorSignChoice refs flag).execute Reference state = state.mapClassical (fun entry =>
      ((numeratorSignArmStep refs flag entry.1).1,
        (entry.2, (numeratorSignArmStep refs flag entry.1).2))) := by
  cases flag with
  | bit flag =>
    cases flag <;>
      simp only [numeratorSignChoice, numeratorSignArmStep, magnitudeArm, magnitudeArmStep,
        Circuit.execute_id_mapClassical, Circuit.execute_seq,
        Circuit.execute_classical_mapClassical,
        State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def] <;>
      congr 1 <;> exact Subsingleton.elim _ _

/-- The complete actual branch preserves histories and quantum-reference blocks. -/
theorem numeratorSignInto_execute (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (numeratorSignInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((numeratorSignStep refs entry.1).1, (entry.2, (numeratorSignStep refs entry.1).2))) :=
  Circuit.execute_branch_mapClassical _ _ _ (numeratorSignChoice_execute refs) Reference state

/-- Actual numerator correction changes only the existing numerator cell. -/
theorem numeratorSignInto_callerFrame (refs : Refs ctx width) (store : Store ctx)
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

private theorem unary_read (opcode : Resource.WordUnaryOpcode) (store : Store ctx)
    (input : CInputRef ctx (.unsignedWord width)) (output : CWriteRef ctx (.unsignedWord width)) :
    (store.applyOp (.wordUnary opcode width ctx input output)).read (writeInput output) =
      opcode.eval width (store.read input) :=
  Store.read_applyOp_output store (.wordUnary opcode width ctx input output)

/-- The actual flag chooses the corresponding original integer numerator sign. -/
theorem numeratorSignInto_correct (refs : Refs ctx width) (store : Store ctx) (value : Int)
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
theorem numeratorSignInto_events (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
    (numeratorSignInto refs).eventTrace path =
      if path.1.toBool then
        [.classicalOperation (.wordUnary .complement width),
          .classicalOperation (.wordUnary .increment width)] else [] := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- At most two actual native operations correct the numerator sign. -/
theorem numeratorSignInto_eventCount_le (refs : Refs ctx width)
    (path : (numeratorSignInto refs).Path) :
    ((numeratorSignInto refs).eventTrace path).length ≤ 2 := by
  rw [numeratorSignInto_events]
  split <;> simp only [List.length_cons, List.length_nil] <;> decide

/-- The actual selected correction has unit-duration depth at most two. -/
theorem numeratorSignInto_depth_le (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
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
theorem numeratorSignInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (numeratorSignInto refs).BorrowedRestored Reference state
      ((numeratorSignInto refs).execute Reference state) := by
  apply Circuit.borrowedRestored_branch
  intro flag history _ current
  cases flag with
  | bit flag =>
    cases flag
    · change (Circuit.id ctx).BorrowedRestored Reference current
        ((Circuit.id ctx).execute Reference current)
      rw [Circuit.BorrowedRestored, observeBorrowedAfter_sameContext, Circuit.execute_id]
      exact observeBorrowed_mapHistory current _
    · exact Circuit.borrowedRestored_seq _ _ current
        (Circuit.borrowedRestored_classical _ _) (Circuit.borrowedRestored_classical _ _)

/-- Every actual correction instruction, including the idle arm, retains the caller context. -/
theorem numeratorSignInto_visited (refs : Refs ctx width) (path : (numeratorSignInto refs).Path) :
    (numeratorSignInto refs).visitedContexts path =
      if path.1.toBool then [ctx, ctx] else [ctx] := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeNearestPlaneThird
