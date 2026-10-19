/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Target
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates.Label

/-!
# Exact common coordinates after the independent indexed point action

The mathematical target retains the selected exponent, the common selector
and every arithmetic auxiliary value. Only the two coordinate words change,
by the original controlled point translation. These are properties of the
independent target; the measured circuit realizes it on its supported domain.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution MeasuredUncompute

private lemma pointTarget_fields {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (value : (MeasuredPointAddition.context p.size).register.Index) :
    MeasuredPointAddition.targetPermutation E Q value =
      MeasuredPointAddition.label p.size (pointControl p.size value) (pointSelector p.size value)
        (InPlaceTarget.frameEquiv p.size
          (((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).1,
            if pointControl p.size value = 1 then MeasuredPointAddition.translationWords E Q
              ((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).2
            else ((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).2)) := by
  let fields := (InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)
  have original : MeasuredPointAddition.label p.size (pointControl p.size value)
      (pointSelector p.size value) (InPlaceTarget.frameEquiv p.size (fields.1, fields.2)) =
        value := by
    simpa only [fields, Prod.eta, Equiv.apply_symm_apply] using
      (point_label_decomposition p.size value).symm
  have actual := MeasuredPointAddition.targetPermutation_label E Q (pointControl p.size value)
    (pointSelector p.size value) fields.1 fields.2
  rw [original] at actual
  exact actual

private lemma pointTarget_control {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (value : (MeasuredPointAddition.context p.size).register.Index) :
    pointControl p.size (MeasuredPointAddition.targetPermutation E Q value) =
      pointControl p.size value := by
  rw [pointTarget_fields, pointControl_label]

private lemma pointTarget_selector {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (value : (MeasuredPointAddition.context p.size).register.Index) :
    pointSelector p.size (MeasuredPointAddition.targetPermutation E Q value) =
      pointSelector p.size value := by
  rw [pointTarget_fields, pointSelector_label]

private lemma pointTarget_shared {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (value : (MeasuredPointAddition.context p.size).register.Index) :
    pointSharedBasis p.size (MeasuredPointAddition.targetPermutation E Q value) =
      InPlaceTarget.frameEquiv p.size
        (((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).1,
          if pointControl p.size value = 1 then MeasuredPointAddition.translationWords E Q
            ((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).2
          else ((InPlaceTarget.frameEquiv p.size).symm (pointSharedBasis p.size value)).2) := by
  rw [pointTarget_fields, pointSharedBasis_label]

/-- The selected original exponent retains its exact finite value after the target point step. -/
lemma stepPermutation_control {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    indexedValue p.size count (stepPermutation E Q active value) active.castSucc =
      indexedValue p.size count value active.castSucc := by
  have observed := congrArg (fun pair => pointControl p.size pair.1)
    (pointBasis_stepPermutation E Q active value)
  simpa only [pointBasis_control, pointTarget_control] using observed

/-- The common selector retains its exact finite value after the target point step. -/
lemma stepPermutation_selector {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    indexedValue p.size count (stepPermutation E Q active value) (Fin.last count) =
      indexedValue p.size count value (Fin.last count) := by
  have observed := congrArg (fun pair => pointSelector p.size pair.1)
    (pointBasis_stepPermutation E Q active value)
  simpa only [pointBasis_selector, pointTarget_selector] using observed

/-- Every auxiliary value is retained while the selected translation acts on the shared words. -/
lemma stepPermutation_shared {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) :
    sharedBasis p.size count (stepPermutation E Q active value) =
      InPlaceTarget.frameEquiv p.size
        (((InPlaceTarget.frameEquiv p.size).symm (sharedBasis p.size count value)).1,
          if indexedValue p.size count value active.castSucc = 1 then
            MeasuredPointAddition.translationWords E Q
              ((InPlaceTarget.frameEquiv p.size).symm (sharedBasis p.size count value)).2
          else ((InPlaceTarget.frameEquiv p.size).symm (sharedBasis p.size count value)).2) := by
  have observed := congrArg (fun pair => pointSharedBasis p.size pair.1)
    (pointBasis_stepPermutation E Q active value)
  simpa only [pointBasis_shared, pointTarget_shared, pointBasis_control] using observed

/-- Prepared arithmetic work remains prepared around the exact updated pair of words. -/
lemma stepPermutation_prepared {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count)
    (value : (readyContext p.size count).register.Index) (x y : Fin (2 ^ p.size))
    (prepared : sharedBasis p.size count value = InPlaceTarget.preparedBasis p x y) :
    sharedBasis p.size count (stepPermutation E Q active value) =
      InPlaceTarget.preparedBasis p
        (if indexedValue p.size count value active.castSucc = 1 then
          MeasuredPointAddition.translationWords E Q (x, y) else (x, y)).1
        (if indexedValue p.size count value active.castSucc = 1 then
          MeasuredPointAddition.translationWords E Q (x, y) else (x, y)).2 := by
  rw [stepPermutation_shared, prepared, InPlaceTarget.preparedBasis, Equiv.symm_apply_apply]
  rfl

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
