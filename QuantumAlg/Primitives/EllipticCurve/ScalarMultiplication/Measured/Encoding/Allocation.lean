/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Cascade
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation

/-!
# Actual allocation before the converted measured scalar cascade

The supplied runtime context contains only the two original coordinate words
and all original exponent systems. The existing charged initialization adds
the fixed arithmetic work, retains the original finite cells and prepares the
selector. The converted cascade then runs on exactly these complete allocated
entries, using the existing complete output context and no additional bank.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution

/-- The same converted cascade executes on precisely the entries produced by actual allocation. -/
def placedConvertedCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Allocation.after p.size count) (Allocation.after p.size count) :=
  ContextPermutation.localCircuit (convertedCascade E points order coefficient)
    (convertedCascade_isLocal E points order coefficient)
    (Allocation.after p.size count) (Allocation.body_entries p.size count)

/-- Post-allocation conversion and measured execution keep every allocated entry resident. -/
theorem placedConvertedCascade_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ) :
    (placedConvertedCascade E points order coefficient).IsLocal :=
  ContextPermutation.localCircuit_isLocal _ _ _ _

/-- One complete actual circuit allocates work, converts both coordinates, and runs the cascade. -/
def convertedCircuit {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Allocation.before p.size count) (Allocation.after p.size count) :=
  (Allocation.initializeWork p count).seq (placedConvertedCascade E points order coefficient)

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
