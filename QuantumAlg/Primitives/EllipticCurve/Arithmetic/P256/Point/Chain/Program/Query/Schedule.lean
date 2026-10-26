/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Arithmetic.Native.Labels
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Initializer

/-!
# The original selector and six numerical query occurrences

Five ordinary occurrences use the original whole-digit enable. Occurrence
three uses that enable and the negated genuine normal flag. Their field
coordinates are arbitrary, and the selector law also retains the original
arbitrary binary-word domain. These identities describe the existing
queryFieldNext function; they assert no geometric or executable action.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open Execution Arithmetic.Call Arithmetic.Call.Endpoint Window.QueryInsertion

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus clearedInitial Residue.input

private lemma clearedInitial_normal_read (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Window.normalBit.get (clearedInitial input numerator flags address) = flags.2.1 := by
  change (clearedInitial input numerator flags address).1.2.2.1 = _
  rw [clearedInitial_flags]

/-- The same actual selector reads the complete original digit and independent genuine N. -/
lemma querySelected_clearedInitial (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (exceptional : Bool) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    querySelected stream width bounded exceptional (clearedInitial input numerator flags address) =
      if exceptional then divisionEnabled stream width bounded input numerator flags address &&
        !flags.2.1 else divisionEnabled stream width bounded input numerator flags address := by
  simp only [querySelected, divisionEnabled, Control.digitEnabled, clearedInitial_normal_read]

namespace Parameters

variable {ctx : RuntimeCtx .quantum} (parameters : Parameters ctx)

/-- The existing field-coordinate update uses the original enable at every occurrence. -/
lemma queryFieldNext_selected (occurrence : Fin 6) (x y column : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    parameters.queryFieldNext occurrence x y column flags address =
      queryFieldCoordinates occurrence x y (queryTargetValue occurrence x y +
        if (if decide (occurrence.val = 3) then
          parameters.nativeEnableValue x y flags address && !flags.2.1
          else parameters.nativeEnableValue x y flags address) then column else 0) := by
  have selected := querySelected_clearedInitial parameters.stream
    (parameters.highRemaining + parameters.lowWidth) parameters.addressBound
    (decide (occurrence.val = 3)) (Residue.input x) (Residue.input y) flags address
  unfold queryFieldNext nativeEnableValue
  exact congrArg (fun active : Bool =>
    queryFieldCoordinates occurrence x y
      (queryTargetValue occurrence x y + if active then column else 0)) selected

/-- The first actual query updates the original X coordinate under the complete digit. -/
lemma queryFieldNext_0 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 0 x y column flags address =
      (x + if parameters.nativeEnableValue x y flags address then column else 0, y) := by
  have horizontal : (0 : Fin 6).val = 0 ∨ (0 : Fin 6).val = 2 ∨ (0 : Fin 6).val = 4 := by
    decide
  have ordinary : decide ((0 : Fin 6).val = 3) = false := by decide
  rw [parameters.queryFieldNext_selected, ordinary]
  simp only [queryFieldCoordinates, queryTargetValue, if_pos horizontal,
    if_neg Bool.false_ne_true]

/-- The second actual query updates the original Y coordinate under the complete digit. -/
lemma queryFieldNext_1 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 1 x y column flags address =
      (x, y + if parameters.nativeEnableValue x y flags address then column else 0) := by
  have vertical : ¬((1 : Fin 6).val = 0 ∨ (1 : Fin 6).val = 2 ∨ (1 : Fin 6).val = 4) := by
    decide
  have ordinary : decide ((1 : Fin 6).val = 3) = false := by decide
  rw [parameters.queryFieldNext_selected, ordinary]
  simp only [queryFieldCoordinates, queryTargetValue, if_neg vertical,
    if_neg Bool.false_ne_true]

/-- The third actual query updates the original X coordinate before the square subtraction. -/
lemma queryFieldNext_2 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 2 x y column flags address =
      (x + if parameters.nativeEnableValue x y flags address then column else 0, y) := by
  have horizontal : (2 : Fin 6).val = 0 ∨ (2 : Fin 6).val = 2 ∨ (2 : Fin 6).val = 4 := by
    decide
  have ordinary : decide ((2 : Fin 6).val = 3) = false := by decide
  rw [parameters.queryFieldNext_selected, ordinary]
  simp only [queryFieldCoordinates, queryTargetValue, if_pos horizontal,
    if_neg Bool.false_ne_true]

/-- The fourth actual query retains arbitrary original N and uses precisely E and not N. -/
lemma queryFieldNext_3 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 3 x y column flags address =
      (x, y + if parameters.nativeEnableValue x y flags address && !flags.2.1
        then column else 0) := by
  have vertical : ¬((3 : Fin 6).val = 0 ∨ (3 : Fin 6).val = 2 ∨ (3 : Fin 6).val = 4) := by
    decide
  have exceptional : decide ((3 : Fin 6).val = 3) = true := by decide
  rw [parameters.queryFieldNext_selected, exceptional]
  simp only [queryFieldCoordinates, queryTargetValue, if_neg vertical, ↓reduceIte]

/-- The fifth actual query updates the original reflected X coordinate. -/
lemma queryFieldNext_4 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 4 x y column flags address =
      (x + if parameters.nativeEnableValue x y flags address then column else 0, y) := by
  have horizontal : (4 : Fin 6).val = 0 ∨ (4 : Fin 6).val = 2 ∨ (4 : Fin 6).val = 4 := by
    decide
  have ordinary : decide ((4 : Fin 6).val = 3) = false := by decide
  rw [parameters.queryFieldNext_selected, ordinary]
  simp only [queryFieldCoordinates, queryTargetValue, if_pos horizontal,
    if_neg Bool.false_ne_true]

/-- The last actual query updates the original Y coordinate under the same complete digit. -/
lemma queryFieldNext_5 (x y column : ZMod modulus) (flags : Frame.Controls)
    (address : Window.Address) :
    parameters.queryFieldNext 5 x y column flags address =
      (x, y + if parameters.nativeEnableValue x y flags address then column else 0) := by
  have vertical : ¬((5 : Fin 6).val = 0 ∨ (5 : Fin 6).val = 2 ∨ (5 : Fin 6).val = 4) := by
    decide
  have ordinary : decide ((5 : Fin 6).val = 3) = false := by decide
  rw [parameters.queryFieldNext_selected, ordinary]
  simp only [queryFieldCoordinates, queryTargetValue, if_neg vertical,
    if_neg Bool.false_ne_true]

end Parameters

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
