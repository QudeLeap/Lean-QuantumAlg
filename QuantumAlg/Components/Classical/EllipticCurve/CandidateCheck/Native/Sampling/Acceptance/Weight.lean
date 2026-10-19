/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Acceptance
import all QuantumAlg.Core.Execution.State.Effect

/-!
# Exact acceptance and failure mass of the actual persistent attempt

The original first-success rule transports every complete input block
through the actual returned Store. Only positive blocks need the original
public-point interpretation. Zero-mass blocks contribute zero regardless
of their encodings, and no normalization or sampling independence is assumed.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

omit [BitWord.Selected model] in
private lemma actualRecord_effectWeight (code : Circuit model ctx ctx)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H))
    (record : Store ctx × model.HiddenState →
      (Store ctx × model.HiddenState) × code.Path)
    (equation : code.execute environment Reference state = state.mapClassical
      (fun entry =>
        let result := record (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    (code.execute environment Reference state).effectWeight (fun entry => effects entry.1) =
      state.effectWeight (fun entry => effects (record (entry.1, entry.2.1)).1.1) := by
  rw [equation, ExecutionState.effectWeight_mapClassical_decision]

private lemma persistentAttempt_flag_weight
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (flag : Bool) :
    ((persistentAttempt curve modulus sample base target).execute environment Reference
      state).effectWeight
      (fun entry =>
        if (entry.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun entry =>
        if ((entry.1.read
              (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool ||
            decide (SampleAccepted curve modulus basePoint targetPoint
              (entry.1.read (persistentInput width scalarWidth sample)))) = flag then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  obtain ⟨record, execution, stores⟩ := attemptInto_actualRecord (environment := environment)
    curve modulus
    (persistentInput width scalarWidth sample) (persistentInput width scalarWidth base)
    (persistentInput width scalarWidth target) (persistentInverseSuccess ctx width scalarWidth)
    (persistentCandidate ctx width scalarWidth) (persistentReconstruction ctx width scalarWidth)
    (persistentScalar ctx width scalarWidth) (persistentTargetAccepted ctx width scalarWidth)
    (persistentAccepted ctx width scalarWidth) (persistentSelected ctx width scalarWidth)
  have actual := execution Reference state
  change (persistentAttempt curve modulus sample base target).execute environment Reference
    state = _ at actual
  have weighted := actualRecord_effectWeight (environment := environment)
    (persistentAttempt curve modulus sample base target) state record actual
    (fun store =>
      if (store.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
  rw [weighted]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro entry _
  by_cases positive : 0 < (state.block entry).mass
  · have points := represents entry positive
    have latches := persistentAttemptStore_latches (environment := environment)
      curve modulus sample base target
      (entry.1, entry.2.1) basePoint targetPoint points.1 points.2
    have flagEquation :
        ((record (entry.1, entry.2.1)).1.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        ((entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool ||
          decide (SampleAccepted curve modulus basePoint targetPoint
            (entry.1.read (persistentInput width scalarWidth sample)))) := by
      rw [stores, ← persistentAttemptStore_eq]
      apply Bool.eq_iff_iff.mpr
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using latches.1
    simp only [flagEquation]
  · have zeroMass := le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
    dsimp only
    split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero, zeroMass]

/-- Actual acceptance has exactly the original prior-acceptance-or-current-eligibility mass. -/
lemma persistentAttempt_acceptance_weight
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint) :
    ((persistentAttempt curve modulus sample base target).execute environment Reference
      state).effectWeight
      (fun entry =>
        if (entry.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun entry =>
        if (entry.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = true ∨
            SampleAccepted curve modulus basePoint targetPoint
              (entry.1.read (persistentInput width scalarWidth sample)) then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  simpa only [Bool.or_eq_true, decide_eq_true_eq] using
    persistentAttempt_flag_weight curve modulus sample base target basePoint targetPoint state
      represents true

/-- Actual failure has exactly the original unaccepted-and-currently-ineligible mass. -/
lemma persistentAttempt_failure_weight
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < (state.block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint) :
    ((persistentAttempt curve modulus sample base target).execute environment Reference
      state).effectWeight
      (fun entry =>
        if (entry.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) =
      state.effectWeight (fun entry =>
        if (entry.1.read
            (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false ∧
            ¬SampleAccepted curve modulus basePoint targetPoint
              (entry.1.read (persistentInput width scalarWidth sample)) then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  simpa only [Bool.or_eq_false_eq_eq_false_and_eq_false, decide_eq_false_iff_not] using
    persistentAttempt_flag_weight curve modulus sample base target basePoint targetPoint state
      represents false

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
