/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Pure

/-!
# Actual sampling reset has one fixed physical basis on every branch

The complete terminal reset measures and corrects its existing quantum wires.
Every actual store, service state, history and measurement path retains the
same prescribed pure local seed after tracing out an arbitrary reference.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- Every actual reset record prepares the fixed original complete sampling label. -/
theorem samplingReset_pure_fullSelection {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (PublicInput.terminal E exponentWidth) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (record : Store (PublicInput.terminal E exponentWidth) ×
      (ClassicalOracleModel.empty.HiddenState ×
        (History × (samplingReset E fieldTail exponentWidth sameWidth fits seed).Path))) :
    (StatePromise.pure (NormalizedVector.ket
      (R := (PublicInput.terminal E exponentWidth).quantumLayout.selectedRegister Finset.univ)
      ((PublicInput.terminal E exponentWidth).quantumLayout.restrictSelectedBasis
        Finset.univ (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)))).Holds
      (DensityOperator.observeSelection
        (PublicInput.terminal E exponentWidth).quantumLayout Finset.univ Reference
        (((samplingReset E fieldTail exponentWidth sameWidth fits seed).execute
          Reference state).block record)) :=
  QuditShift.resetToBasis_pure_fullSelection
    (samplingResetImplementations E exponentWidth)
    (samplingResetCells E exponentWidth)
    (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed) state record

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
