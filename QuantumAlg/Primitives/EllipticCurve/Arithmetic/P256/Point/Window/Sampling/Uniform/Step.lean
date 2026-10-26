/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Naturality
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Operators
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Prepared
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Bank
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Reset
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Middle
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Factor
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared.Execution

/-!
# Uniform replacement for the actual reset and measured point window

The actual MZ/X reset establishes physical bank zero on every input. Its
reference support and the real allocating Driver's reference naturality
discharge the generic factor-step premises. Only the mathematical source
starts unprepared; there is no arithmetic or physical bank input condition.
Every original Store, service state, measured Path and Reference is retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

namespace Parameters

/-- Actual reset, H and measured middle replace the same current uniform source exactly. -/
lemma sampling_uniform_step (parameters : Parameters ctx) (index : WindowIndex)
    (Reference : Register)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx (SourceRegister.prod Reference) (services.HiddenState × History))
    (sourceZero : ∀ record label, label.2.1 ≠ (0, 0) →
      (state.block record).matrix label label = 0) :
    (parameters.measuredMiddle index).execute environment _
        (((parameters.reset index).execute environment _
          (state.applyUnitary (fun _ => sourcePreparationAction Reference
            (sourceFuture index)))).applyUnitary
              (fun _ => parameters.sourceFeed index Reference)) =
      ((parameters.preparedStage index Reference).runHead environment state).applyUnitary
        (fun _ => savedPreparation (sourceSegments index) Reference
          (sourceTail index Reference)) := by
  have resetSource := parameters.sampling_reset_referenceSupported index environment
    (SourceRegister.prod Reference) (fun label => label.1 = (0, 0)) state sourceZero
  have doubleSupported : ∀ record label,
      ¬doubleZero (parameters.ports index) (sourceSegments index) Reference label →
        (((parameters.reset index).execute environment _ state).block record).matrix
          label label = 0 := by
    intro record label absent
    by_cases bank : (QuantumFourierTransform.Semiclassical.bankCoordinates
        (parameters.ports index).wires
        (parameters.ports index).qubits label.1).1 =
          QuantumFourierTransform.Semiclassical.Partner.zeroBits (index.lowerWidth + 1)
    · apply resetSource record label
      intro zero
      apply absent
      refine ⟨bank, ?_⟩
      rw [zero]
      exact sampling_sourceSegments_zero index
    · exact parameters.sampling_reset_bank_zero index environment state record label bank
  rw [parameters.sampling_sourceFeed_segments index Reference]
  apply window_source_uniform_factor_step (parameters.ports index) (sourceSegments index)
    Reference (sourceFuture index) (sourceTail index Reference)
    (parameters.reset index) (parameters.measuredMiddle index) environment state
  · exact parameters.sampling_reset_referenceNatural index environment
      (SourceRegister.prod Reference)
      (UnitaryOperator.prodTensor (sourceFuture index) (1 : UnitaryOperator Reference)) state
  · exact sampling_source_future_factor index Reference _ resetSource
  · exact doubleSupported
  · intro current
    let later : UnitaryOperator SourceRegister :=
      UnitaryOperator.reindex (S := SourceRegister) (sourceLabelEquiv index).symm
        (segmentTailPreparation index.sourceStart (index.lowerWidth + 1) index.sourceAfter)
    have transport : savedPreparation (ctx := ctx) (sourceSegments index) Reference
          (sourceTail index Reference) = sourcePreparationAction Reference later :=
      window_source_segmentTail_transport (sourceLabelEquiv index) Reference
    rw [transport]
    exact Locality.sourceAction_referenceNatural
      (parameters.sampling_measuredMiddle_referenceNatural index environment)
      Reference later current

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
