/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Fourier
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws
import all QuantumAlg.Components.Classical.Model.BitWord

/-!
# Retained result cells for both complete windowed Fourier streams

The actual two-by-260 result positions are a bijective indexing of 520
retained measurement cells. Both streams share the same physical 854-system
bank, while every result has its own classical storage key.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-- Row-major index of one actual stream and its chronological result bit. -/
def resultIndex (position : QuantumFourierTransform.Semiclassical.Window.BitPosition 260) :
    Fin 520 :=
  ⟨position.1.val * 260 + position.2.val, by omega⟩

/-- Distinct original stream positions never share a retained result cell. -/
lemma resultIndex_injective : Function.Injective resultIndex := by
  intro first second equal
  have values := congrArg Fin.val equal
  dsimp [resultIndex] at values
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

/-- The same 520 literal allocations supply the complete two-stream result ports. -/
def results (ctx : RuntimeCtx .quantum) :
    Fourier.Results (MeasurementCells.context ctx 2 520) where
  cells := fun position => MeasurementCells.reference ctx 2 520 (resultIndex position)
  distinct := by
    intro first second equal
    apply resultIndex_injective
    exact MeasurementCells.reference_key_injective ctx 2 520 equal

/-- Allocate the result bank through the circuit interpreter before sampling. -/
noncomputable def allocate {services : ClassicalOracleModel} (ctx : RuntimeCtx .quantum) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      ctx (MeasurementCells.context ctx 2 520) :=
  MeasurementCells.allocate
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 2 520

end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
