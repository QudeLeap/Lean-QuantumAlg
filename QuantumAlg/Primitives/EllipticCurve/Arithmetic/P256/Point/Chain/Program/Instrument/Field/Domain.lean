/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Instrument.Field.Point
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Schedule

/-!
# The original first arithmetic domain from its selected affine difference

This internal bridge consumes the same selected point and column supplied by
its original table row. Only the original two affine exclusions are needed;
the numerator remains an arbitrary ordinary field coordinate.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
namespace Program.Parameters
noncomputable section
open Execution Window.Sampling Arithmetic.Call.Endpoint
variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)
attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus Residue.input Arithmetic.Call.clearedInitial
  Window.Tables.selectedFieldColumn queryFieldNext nativeEnableValue
  PointFieldState.initialized firstFieldState

private lemma firstFieldState_x (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    (parameters.firstFieldState inputs state address).x =
      state.x + if parameters.nativeEnableValue state.x state.y state.flags address then
        Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
          (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
          (state.initialized address) 0 else 0 := by
  simp only [firstFieldState, differencesFirstCoordinates, PointFieldState.initialized,
    queryFieldNext_0, queryFieldNext_1, Window.QueryColumns.column]
  rfl

private lemma firstFieldState_flags (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    (parameters.firstFieldState inputs state address).flags = state.flags := by
  unfold firstFieldState
  rfl

private lemma firstFieldState_enable (inputs : PointFieldTableInputs parameters)
    (state : PointFieldState) (address : Window.Address) :
    parameters.nativeEnableValue
        (parameters.firstFieldState inputs state address).x
        (parameters.firstFieldState inputs state address).y
        (parameters.firstFieldState inputs state address).flags address =
      parameters.nativeEnableValue state.x state.y state.flags address := by
  rw [parameters.firstFieldState_flags]
  exact parameters.nativeEnableValue_values _ _ _ _ state.flags address

private lemma firstFieldState_activeDomain_of_affine
    (inputs : PointFieldTableInputs parameters) (state : PointFieldState)
    (address : Window.Address) (curve : PrimeFieldShortWeierstrass modulus)
    (first second : AffinePoint curve) (sameX : state.x = first.x)
    (column : Window.Tables.selectedFieldColumn inputs.curve inputs.point parameters.stream
      (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
      (state.initialized address) 0 = -second.x)
    (allowed : MeasuredPointAddition.affineAllowed true first second)
    (active : parameters.nativeEnableValue state.x state.y state.flags address = true) :
    ActiveDomain
      (Residue.input (parameters.firstFieldState inputs state address).x)
      (Residue.input (parameters.firstFieldState inputs state address).y) := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  apply activeDomain_residue
  rw [parameters.firstFieldState_x, active, if_pos rfl, column, sameX]
  exact (by simpa only [MeasuredPointAddition.firstDifference, sub_eq_add_neg] using
    MeasuredPointAddition.firstDifference_ne_zero curve first second allowed)

end
end Program.Parameters
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
