/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Decode
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Source
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Weight
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Initial
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.Induction

/-!
# The actual source effect at the unchanged original good component

The event reads the real paired operand of the existing paid nearest recovery.
The original Store, hidden state, complete History and Reference remain in
that same source execution. Zero good mass is never divided or normalized.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private def sourceEffectGoodStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1)
    {Reference : Register} (reference : NormalizedVector Reference)
    (event : (Fin (2 * Cascade.exponentWidth I) → Bool) → Bool),
    (parameters.sourceEffect Sampling.schedule Reference environment
      (fun record => recordEventEffect (ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (fun store => event (fun position : Fin (2 * Cascade.exponentWidth I) =>
          (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
              (store.read (Sampling.Recovery.pairedInput parameters))).bits
            (Fin.cast (congrArg (fun width : Nat => 2 * width)
              (Cascade.exponentWidth_eq_260 I)) position))) record.1)
      original
      (parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).weight
        (DensityOperator.ofSubnormalizedVector
          (coherentSource I
            (fun branch => EllipticCurve.FullRange.branchAmplitude
              (Cascade.exponentWidth I) branch.val) reference.vec)
          (by exact sourceBranch_good_norm_le_one I (Reference := Reference) reference)) =
      (idealBranchEffect (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
            (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
          (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
            (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
            (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference))

private lemma sourceEffectGoodStatement_proof : sourceEffectGoodStatement := by
  intro ctx services parameters I sameSpec scratch assigned environment History history
    original prepared Reference reference event
  let amplitude : GoodBranch I → ℂ := fun branch =>
    EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val
  let accepted : Sampling.SourceRegister.Index → Bool := fun complete =>
    event (ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
      (decodedFrequency I complete))
  have bounded : ‖coherentSource I amplitude reference.vec‖ ≤ 1 :=
    sourceBranch_good_norm_le_one I (Reference := Reference) reference
  have actualInput :
      (fun store : Store ctx => event (fun position : Fin (2 * Cascade.exponentWidth I) =>
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
            (store.read (Sampling.Recovery.pairedInput parameters))).bits
          (Fin.cast (congrArg (fun width : Nat => 2 * width)
            (Cascade.exponentWidth_eq_260 I)) position))) =
      (fun store => accepted (storedComplete parameters store)) := by
    funext store
    exact congrArg event (pairedInput_original_bits parameters I store)
  have observation := congrArg
    (fun selected : Store ctx → Bool =>
      (parameters.sourceEffect Sampling.schedule Reference environment
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference)) selected record.1)
        original
        (parameters.physicalLabel
          (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
            (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).weight
        (DensityOperator.ofSubnormalizedVector
          (coherentSource I amplitude reference.vec) bounded)) actualInput
  have initial := sourceEffect_suffix_initial (services := services) parameters I environment
    original amplitude (Reference := Reference) reference.vec bounded accepted
  have suffix := suffixValue_eq_completionWeight (services := services) parameters I sameSpec
    scratch assigned environment 0 (Nat.zero_le 34) (Reference := Reference) original prepared
    amplitude reference.vec accepted
  have complete : suffixValue parameters I environment 0 (Nat.zero_le 34)
      original amplitude reference.vec accepted =
      completionWeight parameters I 0 0 (Nat.zero_le 260) (Nat.zero_le 260)
        original.1 amplitude reference.vec accepted := by
    simpa only [firstCount_zero, secondCount_zero] using suffix
  exact observation.trans (initial.trans (complete.trans
    (completionWeight_idealBranchEffect parameters I original.1
      (Reference := Reference) reference event)))


/-- The actual paid decoder's input event has exactly the original good-component weight. -/
lemma sourceEffect_original_good_weight (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1)
    {Reference : Register} (reference : NormalizedVector Reference)
    (event : (Fin (2 * Cascade.exponentWidth I) → Bool) → Bool) :
    (parameters.sourceEffect Sampling.schedule Reference environment
      (fun record => recordEventEffect (ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (fun store => event (fun position : Fin (2 * Cascade.exponentWidth I) =>
          (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
              (store.read (Sampling.Recovery.pairedInput parameters))).bits
            (Fin.cast (congrArg (fun width : Nat => 2 * width)
              (Cascade.exponentWidth_eq_260 I)) position))) record.1)
      original
      (parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).weight
        (DensityOperator.ofSubnormalizedVector
          (coherentSource I
            (fun branch => EllipticCurve.FullRange.branchAmplitude
              (Cascade.exponentWidth I) branch.val) reference.vec)
          (by exact sourceBranch_good_norm_le_one I (Reference := Reference) reference)) =
      (idealBranchEffect (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) event Reference).weight
        (DensityOperator.ofSubnormalizedVector
          (EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
            (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)
          (EllipticCurve.FullRange.Geometry.goodVector_norm_le_one
            (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
            (FullRange.chronologicalAddend I)
            (FullRange.chronologicalFixedSeed I).toGroupPoint reference)) :=
  sourceEffectGoodStatement_proof (services := services) parameters I sameSpec scratch assigned
    environment original prepared (Reference := Reference) reference event

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
