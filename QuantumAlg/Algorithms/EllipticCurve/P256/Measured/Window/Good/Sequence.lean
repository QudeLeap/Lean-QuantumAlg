/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.Step
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prepared
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence.Quadratic
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Quadratic.Scalar

/-!
# The actual coherent good component through its original outcome sequence

The recursive quadratic sum uses the original reset and named-middle
certificates. Only impossible reset outcomes are removed. Every point and
Fourier outcome, original Store, hidden service state and Path remains in
the continuation, with the complete coherent branch vector intact.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

private def actualOutcomeSum (parameters : Sampling.Parameters ctx)
    (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (rest : List Sampling.WindowIndex) {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    {Reference : Register}
    (effects : Circuit.EffectFamily ctx (Sampling.SourceRegister.prod Reference)
      (services.HiddenState × parameters.SourceRecords (services := services)
        (index :: rest) Reference History))
    (vectors : Bits (index.lowerWidth + 1) →
      HilbertVector (ctx.register.prod (Sampling.SourceRegister.prod Reference))) : Real :=
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
      ∑ pointOutcome : point.1, ∑ outcome : Bits (index.lowerWidth + 1),
        Stage.quadraticSum environment (parameters.sourceStages rest Reference)
          (parameters.sourceCertificates Reference environment rest)
          (History := (History × (parameters.reset (services := services)
            index).Path) ×
            (parameters.measuredMiddle (services := services)
              index).Path) effects
          (sourceFullRetainedRecord (ctx := ctx) (services := services)
            (Outcome := point.1 × Bits (index.lowerWidth + 1)) middle.record
            (Instrument.retainedRecord (ctx := ctx) (services := services)
              reset.record original zero)
            (pointOutcome, outcome))
          (vectors outcome)

private def CoherentPrefixQuadraticConsStatement : Prop :=
  ∀ (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (rest : List Sampling.WindowIndex) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (_prepared : Prepared parameters I original.1)
    (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (effects : Circuit.EffectFamily ctx (Sampling.SourceRegister.prod Reference)
      (services.HiddenState × parameters.SourceRecords (services := services)
        (Sampling.chronologicalIndex position :: rest) Reference History)),
    let index := Sampling.chronologicalIndex position
    let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
      (index.lowerWidth + 1) (parameters.wire index) original.1).1
    Stage.quadraticSum environment
        (parameters.sourceStages (index :: rest) Reference)
        (parameters.sourceCertificates Reference environment (index :: rest))
        (History := History) effects original
        (coherentPrefix parameters I position.val position.isLt.le index.sourceStart
          amplitude reference) =
      actualOutcomeSum parameters index environment rest original effects
        (fun outcome => coherentPrefix parameters I (position.val + 1)
          (Nat.succ_le_of_lt position.isLt) index.sourceEnd
          (fun branch => amplitude branch * Sampling.windowScalar parameters index zeroStore
            (sourceBranch I branch.val) outcome) reference)

/-- One real stage advances the complete coherent vector and retains every possible outcome. -/
lemma coherentPrefix_quadratic_cons :
    CoherentPrefixQuadraticConsStatement (ctx := ctx) (services := services) := by
  unfold CoherentPrefixQuadraticConsStatement
  intro parameters I sameSpec scratch position assigned environment rest History historyFinite
    original prepared amplitude Reference reference effects
  unfold actualOutcomeSum
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
  dsimp only
  change (∑ resetOutcome : Sampling.Reset.Outcome (index.lowerWidth + 1) (parameters.wire index),
    ∑ middleOutcome : point.1 × Bits (index.lowerWidth + 1), _) = _
  rw [Finset.sum_eq_single zero]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro pointOutcome _
    apply Finset.sum_congr rfl
    intro outcome _
    have column := coherentPrefix_sourceStep parameters I sameSpec scratch position assigned
      environment original.1 original.2.1
      (Prepared.driverInputValues parameters I original.1 prepared position)
      amplitude reference zero pointOutcome outcome
    rw [if_pos rfl] at column
    exact congrArg (fun vector => Stage.quadraticSum environment
      (parameters.sourceStages rest Reference)
      (parameters.sourceCertificates Reference environment rest) effects _ vector) column
  · intro resetOutcome _ different
    apply Finset.sum_eq_zero
    intro middleOutcome _
    have column := coherentPrefix_sourceStep parameters I sameSpec scratch position assigned
      environment original.1 original.2.1
      (Prepared.driverInputValues parameters I original.1 prepared position)
      amplitude reference resetOutcome middleOutcome.1 middleOutcome.2
    rw [if_neg different] at column
    exact (congrArg (fun vector => Stage.quadraticSum environment
      (parameters.sourceStages rest Reference)
      (parameters.sourceCertificates Reference environment rest) effects _ vector) column).trans
      (Stage.quadraticSum_zero environment (parameters.sourceStages rest Reference)
        (parameters.sourceCertificates Reference environment rest) effects _)
  · intro absent
    exact False.elim (absent (Finset.mem_univ zero))

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
