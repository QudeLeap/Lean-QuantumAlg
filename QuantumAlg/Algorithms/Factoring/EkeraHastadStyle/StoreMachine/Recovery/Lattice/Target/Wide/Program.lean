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

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual native resize followed by precisely the prescribed original preimage shifts. -/
def scaleKInto (refs : PreimageRefs ctx m ell width) : Circuit model ctx ctx :=
  Word.PowerOfTwo.Scale.into (model := model) m refs.k refs.scaled

/-- Actual common-width preimage store and native chronological path. -/
def scaleKStep (refs : PreimageRefs ctx m ell width) (store : Store ctx) :
    Store ctx × (scaleKInto refs).Path :=
  Word.PowerOfTwo.Scale.step (model := model) m refs.k refs.scaled store

/-- Actual preimage loading retains all incoming state blocks, histories and correlations. -/
lemma scaleKInto_execute (refs : PreimageRefs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (scaleKInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := scaleKStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Word.PowerOfTwo.Scale.into_execute m refs.k refs.scaled Reference state

/-- Native scaling gives exactly the original integer preimage when its word fits. -/
lemma scaleKInto_read (refs : PreimageRefs ctx m ell width) (store : Store ctx)
    (sourceFits : ell + m + 1 ≤ width) :
    ((scaleKStep refs store).1.read (writeInput refs.scaled)).toNat =
      2 ^ m * (store.read refs.k).toNat :=
  (Word.PowerOfTwo.Scale.into_read m refs.k refs.scaled store (by omega)).trans (Nat.mul_comm _ _)

/-- Actual native preimage loading retains every read outside the original supplied destination. -/
lemma scaleKInto_callerFrame (refs : PreimageRefs ctx m ell width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : refs.scaled.key ∉ other.storageKeys) :
    (scaleKStep refs store).1.read other = store.read other :=
  Word.PowerOfTwo.Scale.into_callerFrame m refs.k refs.scaled store other avoids

/-- The two original preimage calls execute in their original chronological order. -/
def preimagesInto (refs : Refs ctx m ell width) : Circuit model ctx ctx :=
  .seq (scaleKInto refs.first) (scaleKInto refs.second)

/-- Both actual preimage stores and their complete native paths. -/
def preimagesStep (refs : Refs ctx m ell width) (store : Store ctx) :
    Store ctx × (preimagesInto refs).Path :=
  let first := scaleKStep refs.first store
  let second := scaleKStep refs.second first.1
  (second.1, (first.2, second.2))

/-- Both actual preimages preserve every quantum-reference block and incoming history. -/
lemma preimagesInto_execute (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (preimagesInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := preimagesStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical
    (environment := environment) (scaleKInto refs.first) (scaleKInto refs.second)
    (fun before =>
      let actual := scaleKStep refs.first before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := scaleKStep refs.second before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => scaleKInto_execute refs.first reference current)
    (fun reference _history _ current => scaleKInto_execute refs.second reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Actual scaling of both original sample components precedes actual target centering. -/
def loadTargetInto (refs : Refs ctx m ell width) : Circuit model ctx ctx :=
  .seq (preimagesInto refs) (LatticeTargetPoint.loadTargetPointInto refs.target)

/-- The actual scaled preimage store feeds both actual centered-coordinate calls. -/
def targetStep (refs : Refs ctx m ell width) (store : Store ctx) :
    Store ctx × (loadTargetInto refs).Path :=
  let prepared := preimagesStep refs store
  let target := LatticeTargetPoint.targetPointStep refs.target prepared.1
  (target.1, (prepared.2, target.2))

/-- Actual wide-target loading retains the complete incoming execution state and correlations. -/
lemma loadTargetInto_execute (refs : Refs ctx m ell width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (loadTargetInto refs).execute environment Reference state = state.mapClassical (fun entry =>
      let actual := targetStep refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (environment := environment) (preimagesInto refs)
    (LatticeTargetPoint.loadTargetPointInto refs.target)
    (fun before =>
      let actual := preimagesStep refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := LatticeTargetPoint.targetPointStep (model := model) refs.target before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current => preimagesInto_execute refs reference current)
    (fun reference _history _ current =>
      LatticeTargetPoint.loadTargetPointInto_execute refs.target reference current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine
