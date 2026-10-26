/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.InPlace
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Native.Copy

/-!
# Actual same-port forward on the complete three-word frame

The original numerator is a separate arbitrary quantum word beside the
whole scanned source. The actual native prefix placement preserves it
exactly, with the full small EEA history and scan pool retained. This
constructor is the same-port forward used by point arithmetic, rather
than a compute/copy inverse with the numerator serving as an XOR target.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInPlaceFrame

noncomputable section

/-- Actual same-port forward on the original source/pool prefix beside the unchanged numerator. -/
def forward (modulus : Nat) (nontrivial : 1 < modulus) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (OutputCopy.encoding modulus.size).width).toQuantum :=
  UnitaryCircuit.prodLeft (n := modulus.size) (InPlaceForward.program modulus nontrivial)

/-- All input/numerator correlations retain exactly the complete original same-port source frame. -/
lemma forward_initial (modulus : Nat) (nontrivial : 1 < modulus)
    (environment : OracleModel.empty.Interpretation)
    (input numerator : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus) (pool : Pool modulus.size)
    (addressZero : pool.1 = 0) (prefixZero : pool.2.1 = 0) (borrowZero : pool.2.2 = false) :
    (forward modulus nontrivial).applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
          ((OutputCopy.encoding modulus.size).encode
            ((InitialPortProgram.inputFrame modulus input, pool), numerator)))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((OutputCopy.encoding modulus.size).encode
          ((SharedEEA.InPlaceForward.result modulus input.val positive bounded, pool),
            numerator))) :=
  UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (encoding modulus.size) (BinaryLabelEncoding.finIdentity modulus.size)
    (InPlaceForward.program modulus nontrivial) _ _ numerator
    (InPlaceForward.program_initial modulus nontrivial environment input coprime positive bounded
      pool addressZero prefixZero borrowZero)

/-- All three large words, small history and the scan pool are simultaneously resident. -/
lemma p256_encoding_width : (OutputCopy.encoding 256).width = 836 := by
  change (encoding 256).width + 256 = 836
  rw [Scanned.p256_encoding_width]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.NativeInPlaceFrame
