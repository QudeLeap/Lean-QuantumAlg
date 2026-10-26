/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.SourceState
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Preparation.Remaining

/-!
# The actual recycled-window event uses the original full-range source

The same mathematical zero column is the original complete exponent-square
state. Its arbitrary external Reference is unchanged. The observed program
is the literal actual thirty-four-window sampler with its original Store
and measured histories. This identity makes no good-point or Born claim.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open Execution
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The mathematical prepared column is exactly the original full-q paired source. -/
lemma sampling_uniformSource_fullRange {Reference : Register}
    (reference : NormalizedVector Reference) :
    Sampling.uniformSource reference = EllipticCurve.FullRange.Geometry.sourceState 260 reference :=
  congrArg (fun vector : NormalizedVector (EllipticCurve.FullRange.Geometry.branchRegister 260) =>
    NormalizedVector.prodTensor vector reference)
    (EllipticCurve.FullRange.fullRange_pairedRemainingPreparation_zero 260)

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The same actual34 event is the same original source effect, without an added input premise. -/
lemma sampling_circuit_fullRange_sourceEffect_weight (parameters : Sampling.Parameters ctx)
    {Reference : Register} (reference : NormalizedVector Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (event : Store ctx → Bool) :
    Execution.storeEffectWeight (Sampling.circuit parameters) environment
        (ExecutionState.ofValue original (DensityOperator.ofPure
          (NormalizedVector.prodTensor (NormalizedVector.ket label) reference)))
        (recordEventEffect (ctx.register.prod Reference) event) =
      (parameters.sourceEffect Sampling.schedule Reference environment
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference)) event record.1)
        original label).weight
        (DensityOperator.ofPure (EllipticCurve.FullRange.Geometry.sourceState 260 reference)) := by
  have actual := Sampling.sampling_circuit_sourceEffect_weight parameters reference environment
    original label event
  have source := congrArg (fun vector : NormalizedVector (Sampling.SourceRegister.prod Reference) =>
    (parameters.sourceEffect Sampling.schedule Reference environment
      (fun record => recordEventEffect
        (ctx.register.prod (Sampling.SourceRegister.prod Reference)) event record.1)
      original label).weight (DensityOperator.ofPure vector))
    (sampling_uniformSource_fullRange reference)
  exact actual.trans source

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
