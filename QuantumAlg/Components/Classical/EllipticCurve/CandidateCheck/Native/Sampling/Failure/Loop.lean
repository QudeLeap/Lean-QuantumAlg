/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Failure
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity.Loop
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Prefix

/-!
# Failure contraction along the actual sampled recovery loop

The same prescribed initial state determines every actual prefix. Public-point
representations are used only on positive blocks of those prefixes. A uniform
candidate floor applies to each real unnormalized failure fiber, including
all existing recovery cells, complete histories and quantum references. The
actual finite loop then contracts its failure mass without an independence
assumption or a promise about unrelated public stores.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α
attribute [local irreducible] underPersistent

variable {kind : ProblemKind} {ctx origin : RuntimeCtx kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

private theorem sampledAttempt_failure_on_prefix
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (points : ∀ (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ)
    (bound : ∀ (K : Type) [Fintype K]
      (state : State (persistentCtx ctx width scalarWidth) Reference K),
      state.mass * lower ≤
        ((underPersistent sampleCode supported width scalarWidth).execute
          Reference state).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
                (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)))
    (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((priorCode.seq
        (sampledAttempt sampleCode supported curve modulus sample base target)).execute
          Reference initial) ≤
      (1 - lower) *
        persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
          (priorCode.execute Reference initial) := by
  let localCode := underPersistent sampleCode supported width scalarWidth
  let state := priorCode.execute Reference initial
  have represented : storeSupported (localCode.execute Reference state) (fun store =>
      PointRepresents curve (store.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (store.read (persistentInput width scalarWidth target)) targetPoint) :=
    (storeSupported_seq priorCode localCode initial _).mp (points (priorCode.seq localCode))
  have step := sampledAttempt_failure_weight_le sampleCode supported curve modulus sample
    base target basePoint targetPoint state represented lower (bound (H × priorCode.Path) _)
  exact (storedWeight_seq priorCode
    (sampledAttempt sampleCode supported curve modulus sample base target) initial
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans_le
        step

/-- Actual-prefix point support and a uniform candidate floor contract the real finite loop. -/
theorem sampledAttempts_failure_weight_le_on_prefix
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal) (count : Nat)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H] (initial : State origin Reference H)
    (points : ∀ (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) entry,
      0 < ((priorCode.execute Reference initial).block entry).mass →
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
        PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ) (atMostOne : lower ≤ 1)
    (bound : ∀ (K : Type) [Fintype K]
      (state : State (persistentCtx ctx width scalarWidth) Reference K),
      state.mass * lower ≤
        ((underPersistent sampleCode supported width scalarWidth).execute
          Reference state).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
                (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)))
    (priorCode : Circuit origin (persistentCtx ctx width scalarWidth)) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((priorCode.seq
        (sampledAttempts sampleCode supported count curve modulus sample base target)).execute
          Reference initial) ≤
      (1 - lower) ^ count *
        persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
          (priorCode.execute Reference initial) := by
  exact Circuit.forRange_effectWeight_le_on_actual_prefix initial count
    (fun _ => sampledAttempt sampleCode supported curve modulus sample base target)
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
    (1 - lower) (sub_nonneg.mpr atMostOne)
    (fun current _ => sampledAttempt_failure_on_prefix sampleCode supported curve modulus sample
      base target basePoint targetPoint initial points lower bound current) priorCode

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
