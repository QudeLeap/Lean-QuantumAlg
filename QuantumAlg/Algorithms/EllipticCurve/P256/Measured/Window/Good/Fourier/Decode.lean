/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Fourier.Coordinates
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Coordinates

/-!
# The existing paid nearest decoder reads the original Fourier event coordinates

The actual pairedInput is already the operand of the existing persistentAttempt.
This proof transports its read bits to the original width and executes no decoder.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

/-- The actual paired input supplies exactly the original-width Fourier event coordinates. -/
lemma pairedInput_original_bits {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (store : Execution.Store ctx) :
    (fun position : Fin (2 * Cascade.exponentWidth I) =>
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.measuredDecodeInput
          (store.read (Sampling.Recovery.pairedInput parameters))).bits
        (Fin.cast (congrArg (fun width : Nat => 2 * width)
          (Cascade.exponentWidth_eq_260 I)) position)) =
      ExceptionalOffsetAveraging.pairedBigEndianSelected (Cascade.exponentWidth I)
        (decodedFrequency I (storedComplete parameters store)) := by
  funext position
  have physical := congrFun (Sampling.Recovery.pairedInput_frequency_bits parameters store)
    (Fin.cast (congrArg (fun width : Nat => 2 * width)
      (Cascade.exponentWidth_eq_260 I)) position)
  have decoded := congrArg
    (fun source : Sampling.SourceRegister.Index =>
      ExceptionalOffsetAveraging.pairedBigEndianSelected 260 source
        (Fin.cast (congrArg (fun width : Nat => 2 * width)
          (Cascade.exponentWidth_eq_260 I)) position))
    (decodedFrequency_stored parameters I store).symm
  exact physical.trans (decoded.trans
    (sourceBranch_selectedBits I (decodedFrequency I (storedComplete parameters store)) position))

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
