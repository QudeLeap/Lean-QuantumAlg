/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Controls

/-!
# Complete point labels read from the common measured scalar context

Every selected point basis consists exactly of the selected original exponent,
the common selector and the common arithmetic basis. These are equalities of
full basis labels, so the original point admissibility condition transfers
without introducing a separate state or workspace premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

/-- Every complete point basis reconstructs from its original control, selector and arithmetic. -/
theorem point_label_decomposition (width : Nat)
    (value : (MeasuredPointAddition.context width).register.Index) :
    value = MeasuredPointAddition.label width (pointControl width value)
      (pointSelector width value) (pointSharedBasis width value) := by
  simp only [pointControl, pointSelector, pointSharedBasis, MeasuredPointAddition.label,
    InPlaceControlled.label, Equiv.symm_apply_apply, Prod.eta]

/-- The reconstructed point label has exactly the supplied finite control. -/
theorem pointControl_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    pointControl width (MeasuredPointAddition.label width control selector original) = control := by
  simp only [pointControl, MeasuredPointAddition.label, InPlaceControlled.label,
    Equiv.apply_symm_apply]

/-- The reconstructed point label has exactly the supplied finite selector. -/
theorem pointSelector_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    pointSelector width (MeasuredPointAddition.label width control selector original) =
      selector := by
  simp only [pointSelector, MeasuredPointAddition.label, Equiv.apply_symm_apply]

/-- The reconstructed point label retains the entire supplied arithmetic basis. -/
theorem pointSharedBasis_label (width : Nat) (control selector : Fin 2)
    (original : (NumeratorMeasurement.context width).register.Index) :
    pointSharedBasis width (MeasuredPointAddition.label width control selector original) =
      original := by
  simp only [pointSharedBasis, MeasuredPointAddition.label, InPlaceControlled.label,
    Equiv.apply_symm_apply]

/-- The actual indexed point view is exactly its original complete point label. -/
theorem pointBasis_label (width : Nat) {count : Nat} (active : Fin count)
    (value : (readyContext width count).register.Index) :
    (pointBasis width active value).1 =
      MeasuredPointAddition.label width (indexedValue width count value active.castSucc)
        (indexedValue width count value (Fin.last count)) (sharedBasis width count value) := by
  rw [point_label_decomposition width (pointBasis width active value).1,
    pointBasis_control, pointBasis_selector, pointBasis_shared]

/-- Step admissibility reads the original selected exponent, selector and shared arithmetic. -/
theorem stepAdmissible_label {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    stepAdmissible E Q active value ↔ MeasuredPointAddition.admissible E Q
      (MeasuredPointAddition.label p.size (indexedValue p.size count value active.castSucc)
        (indexedValue p.size count value (Fin.last count)) (sharedBasis p.size count value)) := by
  rw [stepAdmissible_pointBasis, pointBasis_label]

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
