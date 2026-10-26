/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Instrument
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Quadratic

/-!
# Specified component certificates of the actual full window sequence

Each source stage uses the specified original reset and named measured-middle
instruments. The mathematical source feed remains outside the physical
circuit syntax. No point-correctness or probability hypothesis supplies any
part of these actual interpreter certificates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

variable (parameters : Parameters ctx)

/-- The two original circuit instruments surround one mathematical source feed. -/
def sourceStageInstruments (index : WindowIndex) (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Stage.Instruments (parameters.sourceStage index Reference) environment := by
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  exact
    { FirstOutcome := Reset.Outcome (index.lowerWidth + 1) (parameters.wire index)
      firstFinite := inferInstance
      LastOutcome := point.1 × Bits (index.lowerWidth + 1)
      lastFinite := inferInstance
      head := Reset.instrument parameters index environment
      tail := Locality.namedMeasuredMiddleInstrument parameters index environment }

/-- The same ordered actual window list has its original component certificates. -/
def sourceCertificates (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    (indices : List WindowIndex) →
      Stage.Certificates environment (parameters.sourceStages indices Reference)
  | [] => ⟨()⟩
  | index :: rest =>
      (parameters.sourceStageInstruments index Reference environment,
        sourceCertificates Reference environment rest)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
