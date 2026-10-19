/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Preparation
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade
import all QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction

/-!
# Measured scalar cascade on the actual allocated workspace

The indexed measured point calls execute on the complete entries produced by
the real zero allocation, fixed-bit loading and retained-cell prefix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution ContextUnion MeasuredUncompute MAU.Inversion.SharedEEA

/-- Execute the same actual measured cascade on the entries produced by initialization. -/
def placedCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (after p.size count) (after p.size count) allowAllocation :=
  .embed (ContextEmbedding.alongPermutation (body_entries p.size count))
    (cascade E points order false)

/-- One actual circuit initializes its work and executes the prescribed indexed point cascade. -/
def circuit {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (before p.size count) (after p.size count) :=
  .seq (initializeWork p count) (placedCascade E points order)

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
