/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Sampling.Failure
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Nearest.Sampling.Validity.Loop
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Prefix

/-!
# Conditional failure contraction for actual nearest-recovery attempts

The actual sampler preserves the retained failure bit.  The paid nearest
recovery and candidate verification feed the actual first-success selector.
A uniform candidate floor on arbitrary dirty History fibers therefore
contracts the same physical loop without an independence or caller-reset
assumption.  No subgroup-truncated sampling bound is reused.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular
open CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α
attribute [local irreducible] sampleUnderPersistent

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx origin : RuntimeCtx model.kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

private lemma sampledAttempt_failure_on_prefix
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H))
    (points : ∀ (priorCode : Circuit model origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute environment Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ)
    (bound : ∀ (K : Type) [Fintype K]
      (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × K)),
      state.mass * lower ≤
        ((sampleUnderPersistent sampleCode width scalarWidth).execute environment
          Reference state).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
                (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)))
    (priorCode : Circuit model origin (persistentCtx ctx width scalarWidth)) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((priorCode.seq
        (sampledAttempt sampleCode curve modulus sample base target)).execute environment
          Reference initial) ≤
      (1 - lower) *
        persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
          (priorCode.execute environment Reference initial) := by
  let localCode := sampleUnderPersistent sampleCode width scalarWidth
  let state := priorCode.execute environment Reference initial
  have represented : storeSupported (localCode.execute environment Reference state) (fun store =>
      PointRepresents curve (store.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (store.read (persistentInput width scalarWidth target)) targetPoint) :=
    (storeSupported_seq priorCode localCode initial _).mp (points (priorCode.seq localCode))
  have step := sampledAttempt_failure_weight_le (environment := environment)
    sampleCode curve modulus sample
    base target basePoint targetPoint state represented lower (bound (H × priorCode.Path) _)
  exact (storedWeight_seq priorCode
    (sampledAttempt sampleCode curve modulus sample base target) initial
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans_le
        step

/-- Actual-prefix point support and a uniform candidate floor contract the real finite loop. -/
lemma sampledAttempts_failure_weight_le_on_prefix
    (sampleCode : Circuit model ctx ctx false) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (initial : State origin Reference (model.HiddenState × H))
    (points : ∀ (priorCode : Circuit model origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute environment Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ) (atMostOne : lower ≤ 1)
    (bound : ∀ (K : Type) [Fintype K]
      (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × K)),
      state.mass * lower ≤
        ((sampleUnderPersistent sampleCode width scalarWidth).execute environment
          Reference state).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
                (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)))
    (priorCode : Circuit model origin (persistentCtx ctx width scalarWidth)) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((priorCode.seq
        (sampledAttempts sampleCode count curve modulus sample base target)).execute environment
          Reference initial) ≤
      (1 - lower) ^ count *
        persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
          (priorCode.execute environment Reference initial) := by
  exact Circuit.forRange_effectWeight_le_on_actual_prefix initial count
    (fun _ => sampledAttempt sampleCode curve modulus sample base target)
    environment
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
    (1 - lower) (sub_nonneg.mpr atMostOne)
    (fun current _ => sampledAttempt_failure_on_prefix sampleCode curve modulus sample
      base target basePoint targetPoint initial points lower bound current) priorCode

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native.Nearest
