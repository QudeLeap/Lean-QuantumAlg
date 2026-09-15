/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Program
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade

/-!
# Actual coordinate conversion around the measured scalar cascade

The complete circuit first multiplies X and Y by the inverse selected unit,
executes the measured point cascade, and then multiplies both coordinates by
the selected unit. All four real multiplier calls use the existing A word
on the same complete runtime context. The definition alone makes no claim
that these conversions establish an arithmetic input condition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute

/-- Actual inverse conversion, measured point calls, then forward conversion share one context. -/
def convertedCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) :
    Circuit (readyContext p.size count) (readyContext p.size count) :=
  (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).seq
    ((cascade E points order).seq
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient))

/-- Conversion and every measured call retain precisely the complete original ready context. -/
theorem convertedCascade_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) :
    (convertedCascade E points order coefficient).IsLocal :=
  ⟨pairCircuit_isLocal _ _ _ _, cascade_isLocal E points order,
    pairCircuit_isLocal _ _ _ _⟩

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
