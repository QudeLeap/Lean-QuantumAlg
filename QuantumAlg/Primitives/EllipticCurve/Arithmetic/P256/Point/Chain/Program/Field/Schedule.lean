/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Schedule
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Field.Schedule

/-!
# The original point-program coordinate and normal-flag schedule

Six existing query updates surround the original division, square, normal
selection, multiplication and reflection. Both normal toggles remain in
their actual order. This is a total mathematical label calculation, with
no circuit action, table-value certificate, resource or probability claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program.Parameters

noncomputable section

open Execution Arithmetic.Call.Endpoint

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

attribute [local irreducible] modulus

/-- Existing coordinate updates in the same chronological point-program order. -/
def fieldProgramOutput (columns : Fin 5 → ZMod modulus) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    (ZMod modulus × ZMod modulus) × Frame.Controls :=
  let first := parameters.queryFieldNext 0 x y (columns 0) flags address
  let second := parameters.queryFieldNext 1 first.1 first.2 (columns 1) flags address
  let divided : ZMod modulus × ZMod modulus :=
    (second.1, if parameters.nativeEnableValue second.1 second.2 flags address
      then second.2 * second.1⁻¹ else second.2)
  let third := parameters.queryFieldNext 2 divided.1 divided.2 (columns 2) flags address
  let squared := parameters.nativeSquareValue third.1 third.2 flags address
  let normalFlags := parameters.nativeNormalFlags squared third.2 flags address
  let multiplied := if normalFlags.2.1 then third.2 * squared else third.2
  let fourth := parameters.queryFieldNext 3 squared multiplied (columns 3) normalFlags address
  let restoredFlags := parameters.nativeNormalFlags fourth.1 fourth.2 normalFlags address
  let reflected := parameters.nativeReflectionValue fourth.1 fourth.2 normalFlags address
  let fifth := parameters.queryFieldNext 4 reflected fourth.2 (columns 4) restoredFlags address
  let sixth := parameters.queryFieldNext 5 fifth.1 fifth.2 (columns 1) restoredFlags address
  (sixth, restoredFlags)

private def columnProgramOutput (columns : Fin 5 → ZMod modulus) (enabled : Bool)
    (x y : ZMod modulus) (flags : Frame.Controls) :
    (ZMod modulus × ZMod modulus) × Frame.Controls :=
  let firstX := x + if enabled then columns 0 else 0
  let firstY := y + if enabled then columns 1 else 0
  let quotient := if enabled then firstY * firstX⁻¹ else firstY
  let shiftedX := firstX + if enabled then columns 2 else 0
  let secondX := if enabled then shiftedX - quotient ^ 2 else shiftedX
  let predicate := enabled && !decide (secondX = 0)
  let normal := flags.2.1 ^^ predicate
  let normalFlags := setNormal flags normal
  let product := if normal then quotient * secondX else quotient
  let exceptionalY := product + if enabled && !normal then columns 3 else 0
  let restoredFlags := setNormal normalFlags (normal ^^ predicate)
  let reflectedX := if enabled then -1 - secondX else secondX
  let finalX := reflectedX + if enabled then columns 4 else 0
  let finalY := exceptionalY + if enabled then columns 1 else 0
  ((finalX, finalY), restoredFlags)

private lemma normalFlag_setNormal (flags : Frame.Controls) (value : Bool) :
    (setNormal flags value).2.1 = value := rfl

private lemma reflag_twice (flags : Frame.Controls) (predicate : Bool) :
    setNormal (setNormal flags (flags.2.1 ^^ predicate))
      ((flags.2.1 ^^ predicate) ^^ predicate) = flags := by
  rcases flags with ⟨control, normal, work⟩
  cases normal <;> cases predicate <;> rfl

private lemma predicate_eq_normalControl (enabled : Bool) (difference : ZMod modulus) :
    (enabled && !decide (difference = 0)) =
      MeasuredPointAddition.normalControl enabled difference := by
  by_cases zero : difference = 0 <;>
    simp [MeasuredPointAddition.normalControl, zero]

private lemma columnProgramOutput_flags (columns : Fin 5 → ZMod modulus) (enabled : Bool)
    (x y : ZMod modulus) (flags : Frame.Controls) :
    (columnProgramOutput columns enabled x y flags).2 = flags := by
  exact reflag_twice flags _

attribute [local irreducible] nativeEnableValue setNormal

private lemma fieldProgramOutput_eq_columns (columns : Fin 5 → ZMod modulus)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    parameters.fieldProgramOutput columns x y flags address =
      columnProgramOutput columns (parameters.nativeEnableValue x y flags address) x y flags := by
  have values (first second : ZMod modulus) :
      parameters.nativeEnableValue first second flags address =
        parameters.nativeEnableValue x y flags address :=
    parameters.nativeEnableValue_values first second x y flags address
  simp only [fieldProgramOutput, parameters.queryFieldNext_0, parameters.queryFieldNext_1,
    parameters.queryFieldNext_2, parameters.queryFieldNext_3, parameters.queryFieldNext_4,
    parameters.queryFieldNext_5, nativeSquareValue, nativeNormalFlags, nativeReflectionValue,
    parameters.nativeEnableValue_setNormal, values, normalFlag_setNormal, columnProgramOutput]

/-- The genuine normal predicate is toggled twice on the same X, for arbitrary original N. -/
lemma fieldProgramOutput_flags (columns : Fin 5 → ZMod modulus) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    (parameters.fieldProgramOutput columns x y flags address).2 = flags := by
  rw [parameters.fieldProgramOutput_eq_columns]
  exact columnProgramOutput_flags columns _ x y flags

/-- An unselected digit preserves arbitrary field coordinates and columns from original N zero. -/
lemma fieldProgramOutput_false (columns : Fin 5 → ZMod modulus) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) (normalZero : flags.2.1 = false)
    (disabled : parameters.nativeEnableValue x y flags address = false) :
    parameters.fieldProgramOutput columns x y flags address = ((x, y), flags) := by
  rw [parameters.fieldProgramOutput_eq_columns, disabled]
  simpa only [columnProgramOutput, Bool.false_eq_true, if_false, add_zero, Bool.false_and,
    Bool.xor_false, normalZero] using congrArg (fun current => ((x, y), current))
      (reflag_twice flags false)

/-- The actual label calculation is the independent total field schedule with its original flags. -/
lemma fieldProgramOutput_fieldSchedule (curve : PrimeFieldShortWeierstrass modulus)
    (point : AffinePoint curve) (x y : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) (normalZero : flags.2.1 = false) :
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    parameters.fieldProgramOutput
        ![-point.x, -point.y, 3 * point.x,
          -MeasuredPointAddition.exceptionalSlope curve point, point.x + 1] x y flags address =
      (MeasuredPointAddition.fieldSchedule curve point
        (parameters.nativeEnableValue x y flags address) x y, flags) := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  rw [parameters.fieldProgramOutput_eq_columns]
  apply Prod.ext
  · simp [columnProgramOutput, MeasuredPointAddition.fieldSchedule, normalZero,
      predicate_eq_normalControl, div_eq_mul_inv]
  · exact columnProgramOutput_flags _ _ x y flags

end

end Program.Parameters

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
