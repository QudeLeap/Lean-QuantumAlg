/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence.Vector
import all QuantumAlg.Core.Base.Gate.Effect.Support

/-!
# The complete actual window effect on its original coherent source vector

This exact identity applies the specified reset and measured-middle
instruments to one raw coherent vector. Every actual outcome, intermediate
Store, service state and Path remains in the recursive sum. A bounded
component retains its original mass without branch conditioning.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The actual source effect is precisely the coherent quadratic sum of its original instruments. -/
lemma sourceEffect_vector_quadraticSum (parameters : Parameters ctx)
    (indices : List WindowIndex) {Reference : Register}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (label : ctx.register.Index)
    (source : HilbertVector (SourceRegister.prod Reference))
    (bounded : ‖source‖ ≤ 1) (event : Store ctx → Bool) :
    (parameters.sourceEffect indices Reference environment
      (fun record => Execution.recordEventEffect
        (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
      original label).weight
        (DensityOperator.ofSubnormalizedVector source bounded) =
      Stage.quadraticSum environment (parameters.sourceStages indices Reference)
        (parameters.sourceCertificates Reference environment indices)
        (fun record => Execution.recordEventEffect
          (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
        original
        (HilbertVector.prodTensor (NormalizedVector.ket (R := ctx.register) label).vec source) := by
  let : Fintype History := Fintype.ofFinite History
  let vector :=
    HilbertVector.prodTensor (NormalizedVector.ket (R := ctx.register) label).vec source
  let density := DensityOperator.ofSubnormalizedVector vector
    (window_source_ket_vector_bounded label source bounded)
  let state := @ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
    (ctx.register.prod (SourceRegister.prod Reference)) (Classical.decEq _) original density
  let observed := Stage.observation environment (parameters.sourceStages indices Reference)
    (History := History)
    (fun record => Execution.recordEventEffect
      (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
  calc
    _ = Stage.storeWeight environment (parameters.sourceStages indices Reference) state
        (fun store => Execution.recordEventEffect
          (ctx.register.prod (SourceRegister.prod Reference)) event store) :=
      sourceEffect_vector_storeWeight parameters indices environment original label source
        bounded event
    _ = state.effectWeight observed :=
      Stage.window_sourceSequence_storeWeight environment
        (parameters.sourceStages indices Reference) state _
    _ = (observed original).weight density :=
      ExecutionState.effectWeight_ofValue_decision (Classical.decEq _) original density observed
    _ = HilbertOperator.quadraticWeight (observed original).matrix vector :=
      Effect.weight_ofSubnormalizedVector (observed original) vector _
    _ = _ := Stage.window_sourceSequence_quadratic environment
      (parameters.sourceStages indices Reference)
      (parameters.sourceCertificates Reference environment indices) _ original vector

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
