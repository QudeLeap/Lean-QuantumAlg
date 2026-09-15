/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Program.Layout

/-!
# Actual native wide short-log target loading

Two native resize-and-shift calls construct the original scaled sample words.
The actual resulting store feeds both centered-coordinate calls, retaining the
original common-width layout and complete incoming quantum-reference state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell width : Nat}

/-- Actual native resize followed by precisely the prescribed original preimage shifts. -/
def scaleKInto (refs : PreimageRefs ctx m ell width) : Circuit ctx ctx :=
  Word.PowerOfTwo.Scale.into m refs.k refs.scaled

/-- Actual common-width preimage store and native chronological path. -/
def scaleKStep (refs : PreimageRefs ctx m ell width) (store : Store ctx) :
    Store ctx × (scaleKInto refs).Path := Word.PowerOfTwo.Scale.step m refs.k refs.scaled store

/-- Actual preimage loading retains all incoming state blocks, histories and correlations. -/
theorem scaleKInto_execute (refs : PreimageRefs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (scaleKInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((scaleKStep refs entry.1).1, (entry.2, (scaleKStep refs entry.1).2))) :=
  Word.PowerOfTwo.Scale.into_execute m refs.k refs.scaled Reference state

/-- Native scaling gives exactly the original integer preimage when its word fits. -/
theorem scaleKInto_read (refs : PreimageRefs ctx m ell width) (store : Store ctx)
    (sourceFits : ell + m + 1 ≤ width) :
    ((scaleKStep refs store).1.read (writeInput refs.scaled)).toNat =
      2 ^ m * (store.read refs.k).toNat :=
  (Word.PowerOfTwo.Scale.into_read m refs.k refs.scaled store (by omega)).trans (Nat.mul_comm _ _)

/-- Actual native preimage loading retains every read outside the original supplied destination. -/
theorem scaleKInto_callerFrame (refs : PreimageRefs ctx m ell width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.scaled.key ∉ other.storageKeys) :
    (scaleKStep refs store).1.read other = store.read other :=
  Word.PowerOfTwo.Scale.into_callerFrame m refs.k refs.scaled store other avoids

/-- The two original preimage calls execute in their original chronological order. -/
def preimagesInto (refs : Refs ctx m ell width) : Circuit ctx ctx :=
  .seq (scaleKInto refs.first) (scaleKInto refs.second)

/-- Both actual preimage stores and their complete native paths. -/
def preimagesStep (refs : Refs ctx m ell width) (store : Store ctx) :
    Store ctx × (preimagesInto refs).Path :=
  let first := scaleKStep refs.first store
  let second := scaleKStep refs.second first.1
  (second.1, (first.2, second.2))

/-- Both actual preimages preserve every quantum-reference block and incoming history. -/
theorem preimagesInto_execute (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (preimagesInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((preimagesStep refs entry.1).1, (entry.2, (preimagesStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (scaleKInto refs.first) (scaleKInto refs.second)
    (scaleKStep refs.first) (scaleKStep refs.second) (scaleKInto_execute refs.first)
    (scaleKInto_execute refs.second) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

/-- Actual scaling of both original sample components precedes actual target centering. -/
def loadTargetInto (refs : Refs ctx m ell width) : Circuit ctx ctx :=
  .seq (preimagesInto refs) (LatticeTargetPoint.loadTargetPointInto refs.target)

/-- The actual scaled preimage store feeds both actual centered-coordinate calls. -/
def targetStep (refs : Refs ctx m ell width) (store : Store ctx) :
    Store ctx × (loadTargetInto refs).Path :=
  let prepared := preimagesStep refs store
  let target := LatticeTargetPoint.targetPointStep refs.target prepared.1
  (target.1, (prepared.2, target.2))

/-- Actual wide-target loading retains the complete incoming execution state and correlations. -/
theorem loadTargetInto_execute (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (loadTargetInto refs).execute Reference state = state.mapClassical (fun entry =>
      ((targetStep refs entry.1).1, (entry.2, (targetStep refs entry.1).2))) := by
  refine (Circuit.execute_seq_mapClassical (preimagesInto refs)
    (LatticeTargetPoint.loadTargetPointInto refs.target) (preimagesStep refs)
    (LatticeTargetPoint.targetPointStep refs.target) (preimagesInto_execute refs)
    (LatticeTargetPoint.loadTargetPointInto_execute refs.target) Reference state).trans ?_
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine
