/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Native.Labels
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Field.Domain
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Correctness

/-!
# Original arithmetic domains from the genuine point-program selectors

An originally zero normal flag can become true only at a nonzero current
X. That implication discharges the original product call's domain only
when it is selected. The first call uses the original affine exclusions
to obtain its nonzero first difference. No second-difference or reverse
domain restriction is added to the reachable exceptional branch.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open Execution Arithmetic.Call.Endpoint

attribute [local irreducible] modulus

namespace Parameters

attribute [local irreducible] nativeEnableValue

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

/-- The genuine normal toggle from original N zero requires nonzero current X when selected. -/
lemma nativeNormalFlags_true_nonzero (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false)
    (selected : (parameters.nativeNormalFlags x y flags address).2.1 = true) : x ≠ 0 := by
  intro zero
  change (flags.2.1 ^^
    (parameters.nativeEnableValue x y flags address && !decide (x = 0))) = true at selected
  simp only [normalZero, zero, decide_true, Bool.not_true,
    Bool.and_false, Bool.xor_false, Bool.false_eq_true] at selected

/-- Only the genuine selected normal branch supplies the original product arithmetic domain. -/
lemma nativeNormalFlags_activeDomain [Fact modulus.Prime] (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) (normalZero : flags.2.1 = false)
    (selected : (parameters.nativeNormalFlags x y flags address).2.1 = true) :
    ActiveDomain (Residue.input x) (Residue.input y) :=
  activeDomain_residue x y
    (parameters.nativeNormalFlags_true_nonzero x y flags address normalZero selected)

end Parameters

/-- The original active affine exclusions discharge the first difference's same call domain. -/
lemma firstDifference_activeDomain (curve : PrimeFieldShortWeierstrass modulus)
    (first second : AffinePoint curve)
    (allowed : MeasuredPointAddition.affineAllowed true first second) :
    ActiveDomain (Residue.input (MeasuredPointAddition.firstDifference first.x second.x))
      (Residue.input (first.y - second.y)) := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  exact activeDomain_residue _ _
    (MeasuredPointAddition.firstDifference_ne_zero curve first second allowed)

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
