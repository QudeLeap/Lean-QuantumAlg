/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Fourier.Scalars
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Inputs

/-!
# Original scalar rows of the actual source window

The real Fourier coefficient is the existing signed partner row, with the
same source digit and the phase read from the original retained prefix.
The actual preceding zero reset preserves that scalar because it preserves
every original result cell.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The actual Fourier scalar uses the incoming stored prefix and original current source digit. -/
def windowScalar (parameters : Parameters ctx) (index : WindowIndex) (before : Store ctx)
    (source : SourceRegister.Index) (outcome : Bits (index.lowerWidth + 1)) : ℂ :=
  (NormalizedVector.invSqrt2 ^ 2048) *
    (star (QFTOperator (index.lowerWidth + 1)
      (decodedWindowFrequency (index.lowerWidth + 1) outcome)
      (parameters.sourcePartition index source).1) *
      Partner.phaseBasis (index.lowerWidth + 1)
        (Partner.suffixPhases true (parameters.ports index).start (index.lowerWidth + 1)
          (fun _ => 1) (Feedback.storedPrefix (parameters.ports index) before))
        ((binaryEquiv (index.lowerWidth + 1)).symm
          (parameters.sourcePartition index source).1))

/-- Each actual scalar is the original partner row with its real incoming prefix phases. -/
lemma windowScalar_fourierRows (parameters : Parameters ctx) (index : WindowIndex)
    (before : Store ctx) (source : SourceRegister.Index)
    (outcome : Bits (index.lowerWidth + 1)) :
    windowScalar parameters index before source outcome =
      (NormalizedVector.invSqrt2 ^ 2048) *
        (Partner.fourierRows true (index.lowerWidth + 1) outcome
            ((binaryEquiv (index.lowerWidth + 1)).symm
              (parameters.sourcePartition index source).1) *
          Partner.phaseBasis (index.lowerWidth + 1)
            (Partner.suffixPhases true (parameters.ports index).start (index.lowerWidth + 1)
              (fun _ => 1) (Feedback.storedPrefix (parameters.ports index) before))
            ((binaryEquiv (index.lowerWidth + 1)).symm
              (parameters.sourcePartition index source).1)) := by
  have row := window_signedSource_frequency_entry (index.lowerWidth + 1) outcome
    ((binaryEquiv (index.lowerWidth + 1)).symm
      (parameters.sourcePartition index source).1)
  rw [Feedback.window_signedSource_partner, Equiv.apply_symm_apply] at row
  unfold windowScalar
  rw [← row]

/-- The actual zero reset retains precisely the prefix used by the later Fourier operation. -/
lemma reset_zero_storedPrefix (parameters : Parameters ctx) (index : WindowIndex)
    (before : Store ctx) :
    Feedback.storedPrefix (parameters.ports index)
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) before).1 =
      Feedback.storedPrefix (parameters.ports index) before := by
  apply storedPrefix_eq_of_past_reads
  intro previous _
  exact reset_zero_result_read parameters index before previous

/-- No extra phase or scalar is introduced by the actual zero-reset record. -/
lemma reset_zero_windowScalar (parameters : Parameters ctx) (index : WindowIndex)
    (before : Store ctx) (source : SourceRegister.Index)
    (outcome : Bits (index.lowerWidth + 1)) :
    windowScalar parameters index
        (parameters.resetParameters.zeroRunRecord (services := services)
          (index.lowerWidth + 1) (parameters.wire index) before).1 source outcome =
      windowScalar parameters index before source outcome := by
  unfold windowScalar
  rw [reset_zero_storedPrefix]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
