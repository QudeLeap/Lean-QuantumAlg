/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Retained
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Frame
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete retained candidate verification and caller frame

Two actual retained allocations feed the original verification record. The
same actual path preserves every complete quantum-reference block and prior
history. Fresh destinations automatically preserve all original structural
reads, without a caller separation or initialization condition.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

open Execution ClassicalAlgorithms.EllipticCurve

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

/-- The real retained entry initializes acceptance first and the scalar point second. -/
def retainedInitialStore (width : Nat) (before : Store ctx) : Store (retainedCtx ctx width) :=
  (before.pushRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh).pushRetained
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh

/-- Both actual allocations preserve each original structural input value. -/
lemma retainedInitialStore_read (width : Nat) (before : Store ctx)
    {shape : CShape} (input : CInputRef ctx shape) :
    (retainedInitialStore width before).read (retainedInput width input) = before.read input :=
  (Store.read_pushRetained_underRetained
    (before.pushRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh
    (input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)).trans
    (Store.read_pushRetained_underRetained before ctx.canonicalFreshKey .bit
      ctx.canonicalFreshKey_fresh input)

/-- The later scalar destination is fresh for every original structural input. -/
lemma retainedScalar_separate (width : Nat) {shape : CShape} (input : CInputRef ctx shape) :
    (retainedScalar ctx width).key ∉ (retainedInput width input).storageKeys :=
  CInputRef.fresh_not_mem_storageKeys_underRetained
    (input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh

/-- The first acceptance destination stays separate after retaining the scalar point. -/
lemma retainedAccepted_separate (width : Nat) {shape : CShape} (input : CInputRef ctx shape) :
    (retainedAccepted ctx width).key ∉ (retainedInput width input).storageKeys := by
  have keys := CInputRef.storageKeys_underRetained
    (input.underRetained ctx.canonicalFreshKey .bit ctx.canonicalFreshKey_fresh)
    (acceptedCtx ctx).canonicalFreshKey (PointShape width)
    (acceptedCtx ctx).canonicalFreshKey_fresh
  have separate := CInputRef.fresh_not_mem_storageKeys_underRetained input ctx.canonicalFreshKey
    .bit ctx.canonicalFreshKey_fresh
  exact fun present => separate (keys ▸ present)

/-- Both actual retained allocations preserve every full quantum-reference block. -/
lemma retainOutputs_execute {model : ExecutionModel} {environment : model.Environment}
    (ctx : RuntimeCtx model.kind) (width : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (retainOutputs ctx width).execute environment Reference state = state.mapClassical (fun entry =>
      (retainedInitialStore width entry.1, (entry.2.1, (entry.2.2, ((), ()))))) := by
  dsimp only [retainOutputs, retainedInitialStore, retainedCtx, acceptedCtx]
  rw [Circuit.execute_seq]
  erw [Circuit.execute_retain, Circuit.execute_retain]
  simp only [State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

/-- The complete actual record includes both real allocations and all original native stages. -/
def retainedStep {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit) :
    Store ctx × model.HiddenState →
      (Store (retainedCtx ctx width) × model.HiddenState) ×
        (retainedCircuit spec candidate base target inverseSuccess reconstruction).Path :=
  fun before =>
    let final := verifyStep (environment := environment) spec (retainedInput width candidate)
      (retainedInput width base)
      (retainedInput width target) (retainedInput width inverseSuccess)
      (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width)
      (retainedInitialStore width before.1, before.2)
    (final.1, (((), ()), final.2))

private lemma three_maps_eq {A B C D : Type}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] {R : Register}
    (firstDecision : DecidableEq B) (secondDecision : DecidableEq C)
    (thirdDecision finalDecision : DecidableEq D) (state : ExecutionState A R)
    (first : A → B) (second : B → C) (third : C → D) :
    @ExecutionState.mapClassical C D _ _ R thirdDecision
      (@ExecutionState.mapClassical B C _ _ R secondDecision
        (@ExecutionState.mapClassical A B _ _ R firstDecision state first) second) third =
      @ExecutionState.mapClassical A D _ _ R finalDecision state (third ∘ second ∘ first) := by
  let : DecidableEq B := firstDecision
  let : DecidableEq C := secondDecision
  let : DecidableEq D := thirdDecision
  rw [ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp]
  exact (Circuit.mapClassical_canonicalDecision thirdDecision state _).trans
    (Circuit.mapClassical_canonicalDecision finalDecision state _).symm

/-- Actual retained verification preserves the same complete reference and actual prior history. -/
lemma retained_execute {model : ExecutionModel} {environment : model.Environment}
  [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (retainedCircuit spec candidate base target inverseSuccess reconstruction).execute environment
      Reference state = state.mapClassical (fun entry =>
        let result := retainedStep (environment := environment) spec candidate base target
          inverseSuccess reconstruction
          (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))) := by
  simp only [retainedCircuit, Circuit.execute_seq]
  erw [retainOutputs_execute, verifyInto_execute]
  simp only [State.mapHistory]
  exact three_maps_eq _ _ _ _ state _ _ _

/-- All original structural reads survive both retained allocations and actual verification. -/
lemma retainedStep_preserves_read {model : ExecutionModel} {environment : model.Environment}
  [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (spec : CurveSpec width)
    (candidate : CInputRef ctx (.unsignedWord scalarWidth))
    (base target : CInputRef ctx (PointShape width))
    (inverseSuccess reconstruction : CInputRef ctx .bit)
    (before : Store ctx) (hidden : model.HiddenState)
    {shape : CShape} (observed : CInputRef ctx shape) :
    (retainedStep (environment := environment) spec candidate base target inverseSuccess
      reconstruction
      (before, hidden)).1.1.read (retainedInput width observed) =
        before.read observed :=
  (verifyStep_preserves_read (environment := environment) spec
    (retainedInput width candidate) (retainedInput width base)
    (retainedInput width target) (retainedInput width inverseSuccess)
    (retainedInput width reconstruction) (retainedScalar ctx width) (retainedAccepted ctx width)
    (retainedInitialStore width before) hidden (retainedInput width observed)
    (retainedScalar_separate width observed) (retainedAccepted_separate width observed)).trans
    (retainedInitialStore_read width before observed)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
