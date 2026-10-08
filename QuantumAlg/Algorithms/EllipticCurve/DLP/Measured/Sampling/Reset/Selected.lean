/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Cleanup
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion.Cleanup

/-!
# Actual sampling reset under the selected native classical language

The circuit used before checked recovery keeps its physical measurement and
fixed complete quantum seed when the bit/word operation model is selected.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail exponentWidth : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (seed : AffinePoint E)

/-- Native bit/word selection retains the original prescribed sampling basis
label on every actual output record. -/
theorem samplingReset_selected_reinitializedAt :
    Circuit.ReinitializedAt (BitWord.selectForCircuit
      (samplingReset E fieldTail exponentWidth sameWidth fits seed))
      ((PublicInput.terminal E exponentWidth).quantumLayout.restrictSelectedBasis
        (PublicInput.terminal E exponentWidth).borrowedSelectionᶜ
        (samplingResetLabel E exponentWidth fieldTail sameWidth fits seed)) :=
  BitWord.selectForCircuit_reinitializedAt
    (samplingReset E fieldTail exponentWidth sameWidth fits seed)
    _ (samplingReset_reinitializedAt E fieldTail exponentWidth sameWidth fits seed)

/-- Native-language selection preserves the actual physical reset certificate. -/
theorem samplingReset_selected_restartCleanup :
    Circuit.RestartCleanup (BitWord.selectForCircuit
      (samplingReset E fieldTail exponentWidth sameWidth fits seed)) :=
  BitWord.selectForCircuit_restartCleanup
    (samplingReset E fieldTail exponentWidth sameWidth fits seed)
    (samplingReset_restartCleanup E fieldTail exponentWidth sameWidth fits seed)
    (PublicInput.terminal_noBorrowedQuantum E exponentWidth)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
