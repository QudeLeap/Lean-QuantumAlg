/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Label

/-!
# Original affine step domain in complete shared-workspace coordinates

The selected point step requires the same prepared arithmetic frame and
zero selector as the original measured point body. Only an active original
exponent requires an affine point distinct from the addend and its negative.
This exact equivalence exposes every requirement for the initialization and
trajectory proofs; it imposes no extra arithmetic nonzero condition.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

/-- The point domain is exactly its actual selector, prepared work and affine exclusions. -/
theorem stepAdmissible_iff {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    stepAdmissible E Q active value ↔
      indexedValue p.size count value (Fin.last count) = 0 ∧
      ∃ x y : Fin (2 ^ p.size),
        sharedBasis p.size count value = InPlaceTarget.preparedBasis p x y ∧
        (indexedValue p.size count value active.castSucc = 1 → ∃ P : AffinePoint E,
          x.val = P.x.val ∧ y.val = P.y.val ∧ P ≠ Q ∧ P ≠ AffinePoint.negate Q) := by
  rw [stepAdmissible_pointBasis]
  constructor
  · rintro ⟨control, x, y, same, valid⟩
    have actualControl := congrArg (pointControl p.size) same
    rw [pointBasis_control, pointControl_label] at actualControl
    have actualSelector := congrArg (pointSelector p.size) same
    rw [pointBasis_selector, pointSelector_label] at actualSelector
    have actualWork := congrArg (pointSharedBasis p.size) same
    rw [pointBasis_shared, pointSharedBasis_label] at actualWork
    refine ⟨actualSelector, x, y, actualWork, ?_⟩
    intro on
    apply valid
    exact actualControl.symm.trans on
  · rintro ⟨selector, x, y, work, valid⟩
    refine ⟨indexedValue p.size count value active.castSucc, x, y, ?_, valid⟩
    rw [pointBasis_label, selector, work]

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
