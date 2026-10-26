/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions

/-!
# Both original prefix rows through each actual retained record

The actual middle advances only its selected stream's exact Fourier row.
The other original row and every branch amplitude remain unchanged. The
only common factor is the actual arithmetic instrument's scalar, whose
complete outcome normalization is proved separately.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood sourceBranch
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

private lemma scalar_first_row (amplitude before other scalar common after : ℂ)
    (active : before * scalar = common * after) :
    amplitude * (before * other) * scalar = common * (amplitude * (after * other)) := by
  calc
    _ = amplitude * other * (before * scalar) := by ring
    _ = _ := by rw [active]; ring

private lemma scalar_second_row (amplitude before other scalar common after : ℂ)
    (active : before * scalar = common * after) :
    amplitude * (other * before) * scalar = common * (amplitude * (other * after)) := by
  calc
    _ = amplitude * other * (before * scalar) := by ring
    _ = _ := by rw [active]; ring

/-- The literal zero reset retains both exact prefix rows of every original branch. -/
lemma prefixAmplitude_reset_zero (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (store : Store ctx) (amplitude : GoodBranch I → ℂ) :
    prefixAmplitude parameters I first second firstBound secondBound
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) store).1 amplitude =
      prefixAmplitude parameters I first second firstBound secondBound store amplitude := by
  funext branch
  unfold prefixAmplitude
  rw [Sampling.reset_zero_streamFourierRow, Sampling.reset_zero_streamFourierRow]

/-- An actual generator-stream outcome advances the first row and retains the second. -/
lemma prefixAmplitude_middle_first (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (firstStream : index.stream = 0) (second : Nat) (secondBound : second ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (amplitude : GoodBranch I → ℂ) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)) (branch : GoodBranch I),
      prefixAmplitude parameters I index.start second (by have := index.within; omega)
          secondBound original.1 amplitude branch *
          Sampling.windowScalar parameters index original.1 (sourceBranch I branch.val)
            outcomes.2 =
        (NormalizedVector.invSqrt2 ^ 2048) *
          prefixAmplitude parameters I (index.lowerWidth + 1 + index.start) second
            (by have := index.within; omega) secondBound
            ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
              original outcomes).1.1 amplitude branch := by
  dsimp only
  intro original outcomes branch
  have active := Sampling.named_middle_stream_row (services := services)
    parameters index environment
    (sourceBranch I branch.val) original outcomes
  simp only [Sampling.sourceValue, firstStream, Fin.val_zero, if_true] at active
  have other := Sampling.named_middle_other_row (services := services)
    parameters index environment 1
    (by rw [firstStream]; decide) second secondBound (sourceBranch I branch.val).2
    original outcomes
  unfold prefixAmplitude
  rw [other]
  exact scalar_first_row _ _ _ _ _ _ active

/-- An actual inverse-target outcome advances the second row and retains the first. -/
lemma prefixAmplitude_middle_second (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (secondStream : index.stream = 1) (first : Nat) (firstBound : first ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (amplitude : GoodBranch I → ℂ) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)) (branch : GoodBranch I),
      prefixAmplitude parameters I first index.start firstBound
          (by have := index.within; omega) original.1 amplitude branch *
          Sampling.windowScalar parameters index original.1 (sourceBranch I branch.val)
            outcomes.2 =
        (NormalizedVector.invSqrt2 ^ 2048) *
          prefixAmplitude parameters I first (index.lowerWidth + 1 + index.start) firstBound
            (by have := index.within; omega)
            ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
              original outcomes).1.1 amplitude branch := by
  dsimp only
  intro original outcomes branch
  have active := Sampling.named_middle_stream_row (services := services)
    parameters index environment
    (sourceBranch I branch.val) original outcomes
  simp only [Sampling.sourceValue, secondStream, Fin.val_one, if_false, Nat.one_ne_zero] at active
  have other := Sampling.named_middle_other_row (services := services)
    parameters index environment 0
    (by rw [secondStream]; decide) first firstBound (sourceBranch I branch.val).1
    original outcomes
  unfold prefixAmplitude
  rw [other]
  exact scalar_second_row _ _ _ _ _ _ active

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
