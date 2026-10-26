/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Schedule
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Completions.Chronological
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.Scalar
import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Core.Execution.Instrument.Recorded
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Instrument

/-!
# Weighted recursion through the same complete coherent suffix

The recursion calls the actual one-stage quadratic theorem. It introduces no
action or probability hypothesis, preserves both real Paths and all prior
History, and extracts only the common scalar of the real arithmetic outcome.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine
  Driver.namedDriverInstrument Sampling.Locality.namedMeasuredMiddleInstrument

private lemma retained_middle_store {ResetPath MiddlePath ResetOutcome MiddleOutcome
    History : Type}
    (resetRecord : Store ctx → ResetOutcome → Store ctx × ResetPath)
    (middleRecord : Store ctx × services.HiddenState → MiddleOutcome →
      (Store ctx × services.HiddenState) × MiddlePath)
    (original : Store ctx × (services.HiddenState × History))
    (resetOutcome : ResetOutcome) (middleOutcome : MiddleOutcome) (zeroStore : Store ctx)
    (sameStore : (resetRecord original.1 resetOutcome).1 = zeroStore) :
    (sourceFullRetainedRecord middleRecord
      (Instrument.retainedRecord (services := services) resetRecord original resetOutcome)
      middleOutcome).1 = (middleRecord (zeroStore, original.2.1) middleOutcome).1.1 := by
  dsimp only [sourceFullRetainedRecord, Instrument.retainedRecord]
  rw [sameStore]

private def prefixAmplitudeRetainedMiddleStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
    let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
      (index.lowerWidth + 1) (parameters.wire index) original.1).1
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      (fun branch : GoodBranch I =>
        prefixAmplitude parameters I (firstCount position.val) (secondCount position.val)
          (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
          original.1 amplitude branch *
          Sampling.windowScalar parameters index zeroStore (sourceBranch I branch.val) outcome) =
        (fun branch : GoodBranch I => (NormalizedVector.invSqrt2 ^ 2048) *
          prefixAmplitude parameters I (firstCount (position.val + 1))
            (secondCount (position.val + 1)) (firstCount_le (position.val + 1))
            (secondCount_le (position.val + 1) (Nat.succ_le_of_lt position.isLt))
            (sourceFullRetainedRecord middle.record
              (Instrument.retainedRecord (services := services) reset.record original zero)
              (pointOutcome, outcome)).1 amplitude branch)

private lemma prefixAmplitude_retained_middle :
    prefixAmplitudeRetainedMiddleStatement := by
  intro ctx services parameters I position environment History original amplitude
  dsimp only
  intro pointOutcome outcome
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  let reset := Sampling.Reset.instrument parameters index environment
  let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
  let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
  let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
    (index.lowerWidth + 1) (parameters.wire index) original.1).1
  have zeroStoreEq : (reset.record original.1 zero).1 = zeroStore :=
    congrArg Prod.fst
      (Sampling.Reset.runInstrument_zero_record parameters.resetParameters environment
        (index.lowerWidth + 1) (parameters.wire index) original.1)
  have nextStore := retained_middle_store reset.record middle.record original zero
    (pointOutcome, outcome) zeroStore zeroStoreEq
  have unchanged := prefixAmplitude_reset_zero (services := services) parameters I index
    (firstCount position.val) (secondCount position.val)
    (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
    original.1 amplitude
  funext branch
  rw [← congrFun unchanged branch, nextStore]
  exact chronologicalPrefix_middle parameters I position environment amplitude
    (zeroStore, original.2.1) (pointOutcome, outcome) branch

private def suffixTailValue (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :=
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  let reset := Sampling.Reset.instrument parameters index environment
  let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
  let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
  let zeroStore := (parameters.resetParameters.zeroRunRecord (services := services)
    (index.lowerWidth + 1) (parameters.wire index) original.1).1
  let currentAmplitude := prefixAmplitude parameters I
    (firstCount position.val) (secondCount position.val)
    (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
    original.1 amplitude
  let rest := Sampling.schedule.drop (position.val + 1)
  fun (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)) =>
    Stage.quadraticSum environment (parameters.sourceStages rest Reference)
      (parameters.sourceCertificates Reference environment rest)
      (History := ((History × (parameters.reset (services := services) index).Path) ×
        (parameters.measuredMiddle (services := services) index).Path))
      (fun record => recordEventEffect
        (ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (fun store => event (storedComplete parameters store)) record.1)
      (sourceFullRetainedRecord middle.record
        (Instrument.retainedRecord (services := services) reset.record original zero)
        (pointOutcome, outcome))
      (coherentPrefix parameters I (position.val + 1) (Nat.succ_le_of_lt position.isLt)
        index.sourceEnd
        (fun branch => currentAmplitude branch *
          Sampling.windowScalar parameters index zeroStore (sourceBranch I branch.val) outcome)
        reference)

private def SuffixValueStepStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (_prepared : Prepared parameters I original.1) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    suffixValue parameters I environment position.val position.isLt.le
      original amplitude reference event =
      ∑ pointOutcome : point.1, ∑ outcome : Bits (index.lowerWidth + 1),
        suffixTailValue parameters I position environment original amplitude reference event
          pointOutcome outcome

private lemma suffixValue_step : SuffixValueStepStatement := by
  intro ctx services parameters I sameSpec scratch position assigned environment History _
    original prepared amplitude Reference reference event
  let index := Sampling.chronologicalIndex position
  let currentAmplitude := prefixAmplitude parameters I
    (firstCount position.val) (secondCount position.val)
    (firstCount_le position.val) (secondCount_le position.val position.isLt.le)
    original.1 amplitude
  let rest := Sampling.schedule.drop (position.val + 1)
  have step := coherentPrefix_quadratic_cons parameters I sameSpec scratch position assigned
    environment rest original prepared currentAmplitude reference
    (fun record => recordEventEffect
      (ctx.register.prod (Sampling.SourceRegister.prod Reference))
      (fun store => event (storedComplete parameters store)) record.1)
  have schedule := congrArg
    (fun indices : List Sampling.WindowIndex =>
      Stage.quadraticSum environment (parameters.sourceStages indices Reference)
        (parameters.sourceCertificates Reference environment indices)
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference))
          (fun store => event (storedComplete parameters store)) record.1)
        original (coherentPrefix parameters I position.val position.isLt.le
          index.sourceStart currentAmplitude reference))
    (schedule_drop_cons position.val position.isLt)
  have initial : suffixValue parameters I environment position.val position.isLt.le
      original amplitude reference event =
      Stage.quadraticSum environment (parameters.sourceStages (index :: rest) Reference)
        (parameters.sourceCertificates Reference environment (index :: rest))
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference))
          (fun store => event (storedComplete parameters store)) record.1)
        original (coherentPrefix parameters I position.val position.isLt.le
          index.sourceStart currentAmplitude reference) := by
    simpa only [suffixValue, index, chronological_sourceStart position,
      currentAmplitude, rest] using schedule
  refine initial.trans ?_
  simp only [actualOutcomeSum, suffixTailValue, index, rest, currentAmplitude] at step ⊢
  exact step

private def SuffixTailValueStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (position : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
    ∀ (pointOutcome : point.1) (outcome : Bits (index.lowerWidth + 1)),
      suffixTailValue parameters I position environment original amplitude reference event
        pointOutcome outcome =
      ‖NormalizedVector.invSqrt2 ^ 2048‖ ^ 2 *
        suffixValue parameters I environment (position.val + 1)
          (Nat.succ_le_of_lt position.isLt)
          (sourceFullRetainedRecord middle.record
            (Instrument.retainedRecord (services := services) reset.record original zero)
            (pointOutcome, outcome)) amplitude reference event

private lemma suffixTailValue_eq : SuffixTailValueStatement := by
  intro ctx services parameters I position environment History _ original amplitude
    Reference reference event
  dsimp only
  intro pointOutcome outcome
  dsimp only [suffixTailValue]
  have coefficients := prefixAmplitude_retained_middle parameters I position environment
    original amplitude pointOutcome outcome
  rw [coefficients, coherentPrefix_amplitude_smul, Stage.quadraticSum_smul]
  congr 1
  simp only [suffixValue, chronological_sourceEnd position]

private def SuffixValueConsStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256) (position : Fin 34)
    (_assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (_prepared : Prepared parameters I original.1) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool),
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
    suffixValue parameters I environment position.val position.isLt.le
        original amplitude reference event =
      ∑ pointOutcome : point.1, ∑ outcome : Bits (index.lowerWidth + 1),
        ‖NormalizedVector.invSqrt2 ^ 2048‖ ^ 2 *
          suffixValue parameters I environment (position.val + 1)
            (Nat.succ_le_of_lt position.isLt)
            (sourceFullRetainedRecord middle.record
              (Instrument.retainedRecord (services := services) reset.record original zero)
              (pointOutcome, outcome)) amplitude reference event

private lemma suffixValueConsStatement_proof : SuffixValueConsStatement := by
  intro ctx services parameters I sameSpec scratch position assigned environment History _
    original prepared amplitude Reference reference event
  dsimp only
  refine (suffixValue_step parameters I sameSpec scratch position assigned environment
    original prepared amplitude reference event).trans ?_
  apply Finset.sum_congr rfl
  intro pointOutcome _
  apply Finset.sum_congr rfl
  intro outcome _
  exact suffixTailValue_eq parameters I position environment original amplitude reference event
    pointOutcome outcome


/-- The same suffix advances one actual record and extracts only the arithmetic norm factor. -/
lemma suffixValue_cons (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256) (position : Fin 34)
    (assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1) (amplitude : GoodBranch I → ℂ)
    {Reference : Register} (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) :
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    let reset := Sampling.Reset.instrument parameters index environment
    let middle := Sampling.Locality.namedMeasuredMiddleInstrument parameters index environment
    let zero := Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
    suffixValue parameters I environment position.val position.isLt.le
        original amplitude reference event =
      ∑ pointOutcome : point.1, ∑ outcome : Bits (index.lowerWidth + 1),
        ‖NormalizedVector.invSqrt2 ^ 2048‖ ^ 2 *
          suffixValue parameters I environment (position.val + 1)
            (Nat.succ_le_of_lt position.isLt)
            (sourceFullRetainedRecord middle.record
              (Instrument.retainedRecord (services := services) reset.record original zero)
              (pointOutcome, outcome)) amplitude reference event :=
  suffixValueConsStatement_proof parameters I sameSpec scratch position assigned environment
    original prepared amplitude reference event


end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
