/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions.Step
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions.Record
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Chronology

/-!
# Both original Fourier rows at each chronological cursor

The unchanged stream schedule specializes the actual row update and
complete-output partition. Arithmetic outcomes stay fixed throughout each
Fourier partition; no quantum action or probability premise is introduced.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood sourceBranch
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

/-- Each actual chronological record advances exactly its selected original Fourier row. -/
lemma chronologicalPrefix_middle (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (amplitude : GoodBranch I → ℂ) :
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ original (outcomes : point.1 × Bits (index.lowerWidth + 1)) (branch : GoodBranch I),
      prefixAmplitude parameters I (firstCount position.val) (secondCount position.val)
          (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
          original.1 amplitude branch *
          Sampling.windowScalar parameters index original.1 (sourceBranch I branch.val)
            outcomes.2 =
        (NormalizedVector.invSqrt2 ^ 2048) *
          prefixAmplitude parameters I (firstCount (position.val + 1))
            (secondCount (position.val + 1)) (firstCount_le (position.val + 1))
            (secondCount_le (position.val + 1) (Nat.succ_le_of_lt position.isLt))
            ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
              original outcomes).1.1 amplitude branch := by
  dsimp only
  intro original outcomes branch
  let index := Sampling.chronologicalIndex position
  by_cases firstStream : index.stream = 0
  · have counts := chronological_first_counts position firstStream
    have advance := counts.2.1
    rw [counts.1] at advance
    simpa only [index, counts.1, advance, counts.2.2] using
      prefixAmplitude_middle_first parameters I index firstStream (secondCount position.val)
        (secondCount_le position.val position.isLt.le) environment amplitude
        original outcomes branch
  · have secondStream : index.stream = 1 := by
      apply Fin.ext
      have range := index.stream.isLt
      have nonzero : index.stream.val ≠ 0 := by
        intro zero
        exact firstStream (Fin.ext zero)
      omega
    have counts := chronological_second_counts position secondStream
    have advance := counts.2.1
    rw [counts.1] at advance
    simpa only [index, counts.1, advance, counts.2.2] using
      prefixAmplitude_middle_second parameters I index secondStream (firstCount position.val)
        (firstCount_le position.val) environment amplitude original outcomes branch

private def chronologicalCompletionStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I (firstCount (position.val + 1))
          (secondCount (position.val + 1)) (firstCount_le (position.val + 1))
          (secondCount_le (position.val + 1) (Nat.succ_le_of_lt position.isLt))
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I (firstCount position.val) (secondCount position.val)
          (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
          before amplitude reference event

private lemma chronologicalCompletionStatement_proof : chronologicalCompletionStatement := by
  intro ctx services parameters I position environment before hidden amplitude Reference reference
    event
  dsimp only
  intro pointOutcome
  let index := Sampling.chronologicalIndex position
  by_cases firstStream : index.stream = 0
  · have counts := chronological_first_counts position firstStream
    have advance := counts.2.1
    rw [counts.1] at advance
    simpa only [index, counts.1, advance, counts.2.2] using
      completionWeight_middle_first parameters I index firstStream (secondCount position.val)
        (secondCount_le position.val position.isLt.le) environment before hidden
        amplitude reference event pointOutcome
  · have secondStream : index.stream = 1 := by
      apply Fin.ext
      have range := index.stream.isLt
      have nonzero : index.stream.val ≠ 0 := by
        intro zero
        exact firstStream (Fin.ext zero)
      omega
    have counts := chronological_second_counts position secondStream
    have advance := counts.2.1
    rw [counts.1] at advance
    simpa only [index, counts.1, advance, counts.2.2] using
      completionWeight_middle_second parameters I index secondStream (firstCount position.val)
        (firstCount_le position.val) environment before hidden amplitude reference event
        pointOutcome

/-- For each fixed arithmetic outcome, Fourier outcomes partition the same complete weight. -/
lemma chronologicalCompletion_middle (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I (firstCount (position.val + 1))
          (secondCount (position.val + 1)) (firstCount_le (position.val + 1))
          (secondCount_le (position.val + 1) (Nat.succ_le_of_lt position.isLt))
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I (firstCount position.val) (secondCount position.val)
          (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
          before amplitude reference event :=
  chronologicalCompletionStatement_proof (ctx := ctx) (services := services)
    parameters I position environment before hidden amplitude reference event

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
