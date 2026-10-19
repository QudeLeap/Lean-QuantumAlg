/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Batch
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Execution
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Selected exponent mass reaches the actual checked batch result

The actual allocation, complete attempt loop and final option pack transfer
every original selected exponent event to the original secret output. The
public point interpretation is required only on positive-mass input blocks.
No condition is imposed on impossible classical records, and every quantum
reference block and previous history remains part of the actual execution.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {count : Nat}

attribute [local irreducible] packBatchResultStep recoveryTailStore recoveryBatchStore
attribute [local irreducible] storeFintype batchResultRead
attribute [local irreducible] RuntimeCtx.canonicalFreshKey

private lemma recoveryTail_observe_execute
    {D : Type} [Fintype D] {width scalarWidth : Nat}
    (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec width)
    (modulus : ClassicalAlgorithms.Modular.ModulusSpec scalarWidth)
    (samples : Fin count → CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width))
    (observe : Store (batchResultCtx ctx width scalarWidth) → D)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((recoveryTail curve modulus samples base target).execute environment Reference
      state).mapClassical
      (fun entry => (observe entry.1, entry.2.2.1)) =
      state.mapClassical (fun entry =>
        (observe (recoveryTailStore (environment := environment) curve modulus samples base target
          (entry.1, entry.2.1)),
          entry.2.2)) := by
  rw [recoveryTail_execute]
  change packBatchResultObservedAfter ctx width scalarWidth observe Reference
    ((recoveryBatch curve modulus samples base target).execute environment Reference state) = _
  rw [packBatchResult_observeAfter]
  unfold packBatchResultExpectedAfter
  have actual := recoveryBatch_observe (environment := environment) (model := model)
    curve modulus samples base target
    (fun stored => observe (packBatchResultStep (model := model) ctx width scalarWidth stored).1)
    Reference state
  refine actual.trans ?_
  exact ExecutionState.executionState_mapClassical_congr state (by
    funext entry
    unfold recoveryTailStore
    rfl)

/-- The original secret encoded in the actual final checked optional-word output. -/
def checkedSecretOutput (problem : KnownOrderProblem E.GroupPoint) (input : SecretInput problem) :
    CShape.Value (.option (.unsignedWord (orderWidth problem))) :=
  .optionSome (CShape.wordOfNat (orderWidth problem) input.secret.val)

private lemma positiveEvent_weight_le {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (before after : C → Prop)
    [DecidablePred before] [DecidablePred after]
    (implies : ∀ entry, 0 < (state.block entry).mass → before entry → after entry) :
    state.effectWeight (fun entry => if before entry then Effect.one R else Effect.zero R) ≤
      state.effectWeight (fun entry => if after entry then Effect.one R else Effect.zero R) := by
  unfold ExecutionState.effectWeight
  apply Finset.sum_le_sum
  intro entry _present
  by_cases positive : 0 < (state.block entry).mass
  · by_cases selected : before entry
    · simp only [selected, implies entry positive selected, if_true, le_refl]
    · simp only [selected, if_false, Effect.weight_zero]
      split_ifs
      · simpa only [Effect.weight_one] using (state.block entry).mass_nonneg
      · simp only [Effect.weight_zero, le_refl]
  · have zeroMass := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    dsimp only
    split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero, zeroMass, le_refl]

attribute [local irreducible] ExecutionState.effectWeight

omit [Fact p.Prime] in
/-- The actual checked event is the observation of the complete deterministic tail record. -/
private lemma recoveryTail_checked_weight_eq (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : Fin count → CInputRef ctx
      (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (base target : CInputRef ctx (PointShape (Canonical.Layout.fieldWidth E)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ((recoveryTail (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
        (fun index => rawRecoveryInput problem (measured index)) base target).execute environment
          Reference state).effectWeight (fun entry =>
        if entry.1.read (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
          Effect.one (Register.prod
            (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
            Reference)
        else Effect.zero (Register.prod
          (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
          Reference)) =
      state.effectWeight (fun entry =>
      if (recoveryTailStore (environment := environment) (model := model)
          (Canonical.Layout.curveSpec E)
          (recoveryModulusSpec problem nontrivial)
          (fun index => rawRecoveryInput problem (measured index)) base target
          (entry.1, entry.2.1)).read
          (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) := by
  let samples := fun index => rawRecoveryInput problem (measured index)
  let record := recoveryTailStore (environment := environment) (model := model)
    (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
  let resultCtx := batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)
  let code := recoveryTail (model := model) (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
  let read := fun stored : Store resultCtx => decide
    (stored.read (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
      checkedSecretOutput problem input)
  let effects := fun value : Bool × History =>
    if value.1 = true then
      Effect.one (Register.prod ctx.register Reference)
    else Effect.zero (Register.prod ctx.register Reference)
  have pushed := ExecutionState.effectWeight_mapClassical_decision
    (@instDecidableEqProd Bool History (Classical.decEq Bool) (Classical.decEq History))
    (code.execute environment Reference state)
    (fun entry => (read entry.1, entry.2.2.1)) effects
  have observed := recoveryTail_observe_execute (environment := environment) (model := model)
    (ctx := ctx)
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    samples base target read Reference (History := History) state
  have observedEffects := congrArg (fun output => output.effectWeight effects) observed
  have direct := ExecutionState.effectWeight_mapClassical_decision
    (@instDecidableEqProd Bool History (Classical.decEq Bool) (Classical.decEq History)) state
    (fun entry => (read (record (entry.1, entry.2.1)), entry.2.2)) effects
  have executedEffects :
      (fun entry : Store resultCtx × (model.HiddenState × (History × code.Path)) =>
        effects (read entry.1, entry.2.2.1)) =
      (fun entry =>
        if entry.1.read (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
          Effect.one (Register.prod resultCtx.register Reference)
        else Effect.zero (Register.prod resultCtx.register Reference)) := by
    funext entry
    by_cases accepted : entry.1.read
        (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
          checkedSecretOutput problem input <;>
      simp [effects, read, accepted, resultCtx] <;> rfl
  have originalEffects :
      (fun entry : Store ctx × (model.HiddenState × History) =>
        effects (read (record (entry.1, entry.2.1)), entry.2.2)) =
      (fun entry =>
        if (record (entry.1, entry.2.1)).read
            (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
              checkedSecretOutput problem input then
          Effect.one (Register.prod ctx.register Reference)
        else Effect.zero (Register.prod ctx.register Reference)) := by
    funext entry
    by_cases accepted : (record (entry.1, entry.2.1)).read
        (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
          checkedSecretOutput problem input <;> simp [effects, read, accepted]
  exact (congrArg (fun effects => (code.execute environment Reference state).effectWeight effects)
      executedEffects).symm.trans
    ((pushed.symm.trans (observedEffects.trans direct)).trans
      (congrArg (fun effects => state.effectWeight effects) originalEffects))

/-- The original selected event is included in the actual record's checked secret event. -/
private lemma recoveryTail_selected_record_weight_le (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : Fin count → CInputRef ctx
      (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (base target : CInputRef ctx (PointShape (Canonical.Layout.fieldWidth E)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read base) problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read target) problem.target.toMathlib) :
    state.effectWeight (fun entry =>
      if ∃ index, selectedExponentEvent problem input
          (QubitReadouts.mask (entry.1.read (measured index))) = true then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) ≤
      state.effectWeight (fun entry =>
      if (recoveryTailStore (environment := environment) (model := model)
          (Canonical.Layout.curveSpec E)
          (recoveryModulusSpec problem nontrivial)
          (fun index => rawRecoveryInput problem (measured index)) base target
          (entry.1, entry.2.1)).read
          (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) := by
  let samples := fun index => rawRecoveryInput problem (measured index)
  let record := recoveryTailStore (environment := environment) (model := model)
    (Canonical.Layout.curveSpec E)
    (recoveryModulusSpec problem nontrivial) samples base target
  have fromInput := positiveEvent_weight_le state
    (fun entry => ∃ index, selectedExponentEvent problem input
      (QubitReadouts.mask (entry.1.read (measured index))) = true)
    (fun entry => (record (entry.1, entry.2.1)).read
      (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
        checkedSecretOutput problem input) (by
      intro entry positive selected
      obtain ⟨baseRep, targetRep⟩ := represents entry positive
      obtain ⟨index, event⟩ := selected
      have eligible := selectedExponentEvent_sampleAccepted problem nontrivial input
        (measured index) entry.1 event
      change (recoveryTailStore (environment := environment) (model := model)
        (Canonical.Layout.curveSpec E)
        (recoveryModulusSpec problem nontrivial) samples base target
        (entry.1, entry.2.1)).read _ = _
      unfold recoveryTailStore recoveryBatchStore recoveryBatchState
      exact (packedRecovery_secret_iff problem nontrivial input samples base target
        entry.1 entry.2.1 baseRep targetRep).mpr ⟨index, eligible⟩)
  exact fromInput

attribute [local irreducible] recoveryTail

/-- Any original selected event contributes to the actual complete batch's secret result. -/
lemma recoveryTail_selected_weight_le (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : Fin count → CInputRef ctx
      (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (base target : CInputRef ctx (PointShape (Canonical.Layout.fieldWidth E)))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read base) problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read target) problem.target.toMathlib) :
    state.effectWeight (fun entry =>
      if ∃ index, selectedExponentEvent problem input
          (QubitReadouts.mask (entry.1.read (measured index))) = true then
        Effect.one (Register.prod ctx.register Reference)
      else Effect.zero (Register.prod ctx.register Reference)) ≤
      ((recoveryTail (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
        (fun index => rawRecoveryInput problem (measured index)) base target).execute environment
          Reference state).effectWeight (fun entry =>
        if entry.1.read (batchResultRead ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)) =
            checkedSecretOutput problem input then
          Effect.one (Register.prod
            (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
            Reference)
        else Effect.zero (Register.prod
          (batchResultCtx ctx (Canonical.Layout.fieldWidth E) (orderWidth problem)).register
          Reference)) := by
  exact (recoveryTail_selected_record_weight_le problem nontrivial input measured base target
    Reference state represents).trans_eq
      (recoveryTail_checked_weight_eq problem nontrivial input measured base target
        Reference state).symm


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
