/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Core.Execution.Instrument.Basic
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Locality.Inverse

/-!
# The original recorded inverse-Fourier word as an actual local instrument

The existing native feedback, H, MZ and correction program supplies its
proved local Kraus rows and literal stored record. The complete physical
complement, service state, History and Reference remain present. This
constructor changes no instruction, outcome convention or resource count.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {allowAllocation : Bool} {totalBits active : Nat}

/-- The same actual corrected readout, with its original finite outcomes and complete Path. -/
def fourierInstrument (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) :
    Execution.Instrument (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports) (Bits active) environment where
  record := inverseStoreRecord (operations := operations) (services := services) ports
  operator := inverseLocalOperator ports
  blocks := by
    intro Reference History _ state result
    exact (window_sourceInverse_local_blocks (allowAllocation := allowAllocation)
      ports environment Reference state result).trans (Execution.sum_condition_decisions _ _ _ _)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
