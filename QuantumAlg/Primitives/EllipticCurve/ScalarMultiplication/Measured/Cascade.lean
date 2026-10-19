/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step

/-!
# Actual finite measured point cascades on one common context

Each prescribed point step consumes its indexed exponent system and reuses
the same resident arithmetic bank, selector and finite measurement cells.
The list order is the actual sequential Circuit order; all complete endpoints
are the identical ready context, including the empty cascade.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

/-- Execute the prescribed indexed point calls in order using one actual shared workspace. -/
def cascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) allowAllocation :=
  match order with
  | [] => .id _
  | active :: remaining =>
      (step E (points active) active allowAllocation).seq
        (cascade E points remaining allowAllocation)

/-- Invoke every indexed exponent exactly once in increasing index order. -/
def fullCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) allowAllocation :=
  cascade E points (List.finRange count) allowAllocation

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
