/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence
import all QuantumAlg.Core.Base.Gate.Effect.FixedInput

/-!
# The actual measured-window list gives an effect on the full exponent square

The physical resets and paid measured Driver middles are the same actual
interpreters. Mathematical source feeds select from one fixed exponent
pair. The full mixed classical records remain present. Compression merely
fixes the real initial quantum label in this observation space; it allocates
no physical source bank. Relating uniform source input to real H preparation,
and proving the good columns, are separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

variable (parameters : Parameters ctx)

/-- One concrete reset/feed/measured-Driver stage, with the original caller references. -/
def sourceStage (index : WindowIndex) (Reference : Register) :
    Stage ctx BitWord.model services (SourceRegister.prod Reference) where
  first := parameters.reset index
  feed := parameters.sourceFeed index Reference
  last := parameters.measuredMiddle index

/-- Structural map of an arbitrary real window list, without expanding its circuit bodies. -/
def sourceStages (indices : List WindowIndex) (Reference : Register) :
    List (Stage ctx BitWord.model services (SourceRegister.prod Reference)) :=
  indices.map (fun index => parameters.sourceStage (services := services) index Reference)

/-- All real window Paths, including the reset before every actual measured middle. -/
abbrev SourceRecords (indices : List WindowIndex) (Reference : Register) (History : Type) :=
  Stage.Records (parameters.sourceStages (services := services) indices Reference) History

/-- Positive contractive observation for the entire actual reset/feed/measured-middle list. -/
def sourceEffect (indices : List WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type}
    (effects : Circuit.EffectFamily ctx (SourceRegister.prod Reference)
      (services.HiddenState × parameters.SourceRecords (services := services)
        indices Reference History))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index) :
    Effect (SourceRegister.prod Reference) :=
  Effect.basisSliceEffect
    (Stage.observation environment (parameters.sourceStages indices Reference) effects original)
    label

/-- Exact weight of this full-source effect on the same represented physical input. -/
lemma sourceEffect_weight (indices : List WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (effects : Circuit.EffectFamily ctx (SourceRegister.prod Reference)
      (services.HiddenState × parameters.SourceRecords (services := services)
        indices Reference History))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (source : NormalizedVector (SourceRegister.prod Reference))
    (input : NormalizedVector (ctx.register.prod (SourceRegister.prod Reference)))
    (represented : ∀ left : ctx.register.Index, ∀ right : (SourceRegister.prod Reference).Index,
      input (left, right) = NormalizedVector.ket (R := ctx.register) label left * source right) :
    (parameters.sourceEffect indices Reference environment effects original label).weight
        (DensityOperator.ofPure source) =
      (Stage.run environment (parameters.sourceStages indices Reference)
        (ExecutionState.ofValue original (DensityOperator.ofPure input))).effectWeight effects := by
  let observed := Stage.observation environment (parameters.sourceStages indices Reference)
    effects
  calc
    _ = (observed original).weight (DensityOperator.ofPure input) :=
      Effect.basisSliceEffect_weight_of_pure (observed original) label source input represented
    _ = (ExecutionState.ofValue original (DensityOperator.ofPure input)).effectWeight observed :=
      (ExecutionState.effectWeight_ofValue_decision _ original _ observed).symm
    _ = _ := (Stage.window_sourceSequence_weight environment
      (parameters.sourceStages indices Reference)
      (ExecutionState.ofValue original (DensityOperator.ofPure input)) effects).symm

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
