/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Naturality
import all QuantumAlg.Core.Execution.Instrument.Support
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Observation
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Driver
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Driver.Support
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Locality.Inverse

/-!
# All-input locality of the actual measured point and Fourier middle

The first child is the original paid five-array allocating point Driver.
The second is its genuine stored-feedback inverse Fourier and same-wire
readout/reset. Composition retains the entire original classical record,
both actual Paths and arbitrary Reference, with no arithmetic admission.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Locality QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

/-- The actual allocating measured middle commutes with every external-reference unitary. -/
lemma sampling_measuredMiddle_referenceNatural (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Execution.ReferenceNatural (parameters.measuredMiddle index)
        environment := by
  refine Execution.ReferenceNatural.seq
    (driver_reference_unitary (parameters.pointParameters index) parameters.frame
      parameters.modulus index.row environment) ?_
  intro Reference operator History _ state
  exact window_sourceInverse_reference_unitary (allowAllocation := true)
    (parameters.ports index) environment Reference operator state

/-- Every real output record of the same measured middle retains arbitrary reference support. -/
lemma sampling_measuredMiddle_referenceSupported (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    Execution.ReferenceSupported (parameters.measuredMiddle index) environment := by
  refine (driver_reference_supported (parameters.pointParameters index) parameters.frame
    parameters.modulus index.row environment).seq ?_
  intro Reference allowed History _ state supported result basis absent
  exact window_sourceInverse_reference_support (allowAllocation := true)
    (parameters.ports index) environment Reference allowed state supported result basis absent

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
