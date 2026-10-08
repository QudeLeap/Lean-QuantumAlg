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
    {count : Nat} (points : Fin count → AffinePoint E) : List (Fin count) →
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count)
  | [] => .id _
  | active :: remaining => (step E (points active) active).seq (cascade E points remaining)

/-- The whole cascade remains in the original local instruction fragment. -/
theorem cascade_isLocal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count)) :
    (cascade E points order).IsLocal := by
  induction order with
  | nil => trivial
  | cons active remaining ih => exact ⟨step_isLocal E (points active) active, ih⟩

/-- Invoke every indexed exponent exactly once in increasing index order. -/
def fullCascade {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) :=
  cascade E points (List.finRange count)

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
