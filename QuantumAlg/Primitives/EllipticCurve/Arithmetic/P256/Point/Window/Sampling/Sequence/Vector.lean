/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation.Vector
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation.Reference

/-!
# Complete window observations on coherent source components

The same bounded raw source vector is observed through the actual reset,
source-feed and measured-middle stages. Its original mass and every complete
record are retained. This equality does not assume point correctness or a
sampling probability, and it prepares no additional physical register.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- Any bounded coherent source component has exactly the same final-Store
event weight in the source effect and the complete actual stage run. -/
lemma sourceEffect_vector_storeWeight (parameters : Parameters ctx)
    (indices : List WindowIndex) {Reference : Register}
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Fintype History]
    (original : Store ctx × (services.HiddenState × History))
    (label : ctx.register.Index)
    (source : HilbertVector (SourceRegister.prod Reference))
    (bounded : ‖source‖ ≤ 1) (event : Store ctx → Bool) :
    (parameters.sourceEffect indices Reference environment
      (fun record => Execution.recordEventEffect
        (ctx.register.prod (SourceRegister.prod Reference)) event record.1)
      original label).weight
        (DensityOperator.ofSubnormalizedVector source bounded) =
      Stage.storeWeight environment (parameters.sourceStages indices Reference)
        (@ExecutionState.ofValue (Store ctx × (services.HiddenState × History)) _
          (ctx.register.prod (SourceRegister.prod Reference)) (Classical.decEq _)
          original (DensityOperator.ofSubnormalizedVector
            (HilbertVector.prodTensor (NormalizedVector.ket (R := ctx.register) label).vec
              source)
            (window_source_ket_vector_bounded label source bounded)))
        (fun store => Execution.recordEventEffect
          (ctx.register.prod (SourceRegister.prod Reference)) event store) := by
  exact window_source_vector_basisSlice_storeWeight environment
    (parameters.sourceStages indices Reference) (Classical.decEq _) original label
    source bounded (fun store => Execution.recordEventEffect
      (ctx.register.prod (SourceRegister.prod Reference)) event store)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
