/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Effect
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Transport
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Uniform
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Floor
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Oversampling

/-!
# The literal actual sampler inherits the original chronological full-range floor

The actual suffix induction and original pure oversampling lemma supply the bound.
No old bitwise execution theorem or actual-backend lower bound is imported.
The source effect and every original record are retained throughout.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open FiniteCyclicDLP.Canonical.Probability (SecretInput)

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The existing paid nearest operand is tested in the original problem's Fourier coordinates. -/
def recoverableSourceEvent (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (store : Store ctx) : Bool :=
  EllipticCurve.FullRange.recoverableExponentEvent
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input
    (fun position : Fin (2 * Cascade.exponentWidth I) =>
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
          (store.read (Sampling.Recovery.pairedInput parameters))).bits
        (Fin.cast (congrArg (fun width : Nat => 2 * width)
          (Cascade.exponentWidth_eq_260 I)) position))

private def samplingReferenceLowerStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (_sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (_assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History))
    (_prepared : Prepared parameters I original.1)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    {Reference : Register} (reference : NormalizedVector Reference),
    (4 : ℝ) / 5 ≤ Execution.storeEffectWeight (Sampling.circuit parameters) environment
      (ExecutionState.ofValue original (DensityOperator.ofPure
        (NormalizedVector.prodTensor
          (NormalizedVector.ket
            (parameters.physicalLabel
              (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
                (FullRange.chronologicalFixedSeed I) (false, false, false) 0))) reference)))
      (recordEventEffect (ctx.register.prod Reference)
        (recoverableSourceEvent parameters I input))

private lemma samplingReferenceLowerStatement_proof : samplingReferenceLowerStatement := by
  intro ctx services parameters I sameSpec scratch assigned environment History history
    original prepared input Reference reference
  let problem := ECDLP.Canonical.problem (Cascade.ecdlpInstance I)
  let : NeZero problem.order := ⟨problem.order_ne_zero⟩
  let label : ctx.register.Index := parameters.physicalLabel
    (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
      (FullRange.chronologicalFixedSeed I) (false, false, false) 0)
  let actual : Effect (Sampling.SourceRegister.prod Reference) :=
    parameters.sourceEffect (services := services) Sampling.schedule Reference environment
      (fun record => recordEventEffect (ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (recoverableSourceEvent parameters I input) record.1) original label
  have sameGood := (sourceWidthEffect_good_weight I (Reference := Reference) reference actual).trans
    (sourceEffect_original_good_weight (services := services) parameters I sameSpec scratch assigned
      environment original prepared (Reference := Reference) reference
      (EllipticCurve.FullRange.recoverableExponentEvent problem input))
  have floor := EllipticCurve.FullRange.fullRange_effect_lower_of_good_weight_at_width problem
    (Cascade.exponentWidth I) rfl
    (FullRange.chronologicalFixedSeed I) input (FullRange.fullRange_oversampling I)
    34 (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
    reference (sourceWidthEffect I actual) sameGood
  have numerical := FullRange.chronologicalFixedSeed_floor_ge I
  have source := sourceWidthEffect_full_weight I (Reference := Reference) reference actual
  have circuit := sampling_circuit_fullRange_sourceEffect_weight (services := services)
    parameters reference environment original label (recoverableSourceEvent parameters I input)
  exact numerical.trans (floor.trans_eq (source.trans circuit.symm))


/-- Every original prepared record and pure Reference has the actual thirty-four-window floor. -/
lemma sampling_circuit_reference_lower (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (assigned : ∀ position : Fin 34,
      Driver.driverScratchReferences
        (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
        (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History))
    (prepared : Prepared parameters I original.1)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    {Reference : Register} (reference : NormalizedVector Reference) :
    (4 : ℝ) / 5 ≤ Execution.storeEffectWeight (Sampling.circuit parameters) environment
      (ExecutionState.ofValue original (DensityOperator.ofPure
        (NormalizedVector.prodTensor
          (NormalizedVector.ket
            (parameters.physicalLabel
              (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
                (FullRange.chronologicalFixedSeed I) (false, false, false) 0))) reference)))
      (recordEventEffect (ctx.register.prod Reference)
        (recoverableSourceEvent parameters I input)) :=
  samplingReferenceLowerStatement_proof (ctx := ctx) (services := services)
    parameters I sameSpec scratch assigned environment original prepared input
    (Reference := Reference) reference

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
