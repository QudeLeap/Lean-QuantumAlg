/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Resources.Batch
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scalar
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit.Resources

/-!
# Width-only arithmetic bounds for the original factoring construction

These numerical functions are independent of any retry interpreter. Their
same-bit specializations and arithmetic bounds do not assert a resource
contract for a replacement execution.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical

/-- Public-width formula for one complete fixed-batch recovery. -/
def retryRecoveryUnitDepthClosedFormBound (N : Nat) : Nat :=
  LatticeRecoveryResources.fixedBatchRecoveryCardBound
    (modulusBits N) (shortLogBits N) (tradeoffBits N)
    (RSA.ShortLogWidths.coordinateWidth N (shortLogBits N) (tradeoffBits N))

/-- Public-width formula for original parameter sampling and sixteen members. -/
def retryRepetitionEventCardClosedFormBound (N : Nat) : Nat :=
  1 + ShorStyle.Canonical.Sampler.samplerClassicalBound (modulusBits N) +
    16 * (1 +
      ShortDLP.CompiledMAU.polynomialPrimitiveBound
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N +
      measurementBits N)

/-- The original batch scalar adds parameter sampling, sixteen members and recovery. -/
def retryBatchEventCardClosedFormBound (N : Nat) : Nat :=
  retryRepetitionEventCardClosedFormBound N +
    (1 + retryRecoveryUnitDepthClosedFormBound N)

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
