/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions.Partition

/-!
# Complete-output partition through each original physical record

The zero reset retains the entire completion sum. For each real point
outcome, the actual measured-middle record partitions the same complete
outputs by its next Fourier block. Neither identity assigns probabilities
to source branches or to retained prefixes.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

/-- The literal zero-reset record retains every original complete-output weight. -/
lemma completionWeight_reset_zero (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (before : Store ctx) (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    completionWeight parameters I first second firstBound secondBound
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) before).1
        amplitude reference event =
      completionWeight parameters I first second firstBound secondBound
        before amplitude reference event := by
  have compatible :
      outputCompatible parameters first second firstBound secondBound
          (parameters.resetParameters.zeroRunRecord (services := services)
            (index.lowerWidth + 1) (parameters.wire index) before).1 =
        outputCompatible parameters first second firstBound secondBound before := by
    funext complete
    unfold outputCompatible
    rw [Sampling.reset_zero_retainedPrefix, Sampling.reset_zero_retainedPrefix]
  unfold completionWeight
  rw [compatible]

private def middleFirstStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (firstStream : index.stream = 0) (second : Nat) (secondBound : second ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool),
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I (index.lowerWidth + 1 + index.start) second
          (by have := index.within; omega) secondBound
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I index.start second (by have := index.within; omega)
          secondBound before amplitude reference event

private lemma middleFirstStatement_proof : middleFirstStatement := by
  intro ctx services parameters I index firstStream second secondBound environment before hidden
    amplitude Reference reference event
  dsimp only
  intro pointOutcome
  apply completionWeight_first_append
  · intro outcome
    have appended := parameters.named_middle_retainedPrefix index environment
      (before, hidden) (pointOutcome, outcome)
    have prior : Feedback.retainedPrefix parameters.results.cells index.stream index.start
        (by have := index.within; omega) before =
      Feedback.storedPrefix (parameters.ports index) before :=
      Feedback.retainedPrefix_before (parameters.ports index) before
    rw [← prior] at appended
    simpa only [firstStream] using appended
  · intro outcome
    have other : (1 : Fin 2) ≠ index.stream := by rw [firstStream]; decide
    exact parameters.named_middle_other_prefix (ctx := ctx) (services := services)
      index environment 1 other second secondBound
      (before, hidden) (pointOutcome, outcome)

/-- Each fixed actual point outcome partitions the same first-stream completions exactly once. -/
lemma completionWeight_middle_first (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (firstStream : index.stream = 0) (second : Nat) (secondBound : second ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I (index.lowerWidth + 1 + index.start) second
          (by have := index.within; omega) secondBound
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I index.start second (by have := index.within; omega)
          secondBound before amplitude reference event :=
  middleFirstStatement_proof (ctx := ctx) (services := services)
    parameters I index firstStream second secondBound environment before hidden
    amplitude reference event

private def middleSecondStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (secondStream : index.stream = 1) (first : Nat) (firstBound : first ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool),
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I first (index.lowerWidth + 1 + index.start)
          firstBound (by have := index.within; omega)
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I first index.start firstBound
          (by have := index.within; omega) before amplitude reference event

private lemma middleSecondStatement_proof : middleSecondStatement := by
  intro ctx services parameters I index secondStream first firstBound environment before hidden
    amplitude Reference reference event
  dsimp only
  intro pointOutcome
  apply completionWeight_second_append
  · intro outcome
    have other : (0 : Fin 2) ≠ index.stream := by rw [secondStream]; decide
    exact parameters.named_middle_other_prefix (ctx := ctx) (services := services)
      index environment 0 other first firstBound
      (before, hidden) (pointOutcome, outcome)
  · intro outcome
    have appended := parameters.named_middle_retainedPrefix index environment
      (before, hidden) (pointOutcome, outcome)
    have prior : Feedback.retainedPrefix parameters.results.cells index.stream index.start
        (by have := index.within; omega) before =
      Feedback.storedPrefix (parameters.ports index) before :=
      Feedback.retainedPrefix_before (parameters.ports index) before
    rw [← prior] at appended
    simpa only [secondStream] using appended

/-- Each fixed actual point outcome partitions the same second-stream completions once. -/
lemma completionWeight_middle_second (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (index : Sampling.WindowIndex)
    (secondStream : index.stream = 1) (first : Nat) (firstBound : first ≤ 260)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    ∀ pointOutcome : point.1,
      (∑ outcome : Bits (index.lowerWidth + 1),
        completionWeight parameters I first (index.lowerWidth + 1 + index.start)
          firstBound (by have := index.within; omega)
          ((Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment).record
            (before, hidden) (pointOutcome, outcome)).1.1 amplitude reference event) =
        completionWeight parameters I first index.start firstBound
          (by have := index.within; omega) before amplitude reference event :=
  middleSecondStatement_proof (ctx := ctx) (services := services)
    parameters I index secondStream first firstBound environment before hidden
    amplitude reference event

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
