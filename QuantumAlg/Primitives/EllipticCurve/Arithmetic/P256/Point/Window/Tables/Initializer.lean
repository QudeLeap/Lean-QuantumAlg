/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Update
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Tables.Residue
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Prepare

/-!
# The original table row on complete initialized point labels

The full stream top and address determine the row, independently of both
arbitrary binary numerical words and the genuine normal flag. The row
width remains symbolic, including width zero, and row zero is retained.
These coordinate identities introduce no executable instructions or
canonicality requirements.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Tables

noncomputable section

open Chain.Arithmetic.Call Chain.Arithmetic.Call.Endpoint
open ClassicalAlgorithms.EllipticCurve ClassicalRoutines.EllipticCurve.WindowTables

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus clearedInitial

private lemma initializer_digit_congr (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator nextInput nextNumerator : Fin (2 ^ modulus.size))
    (flags nextFlags : Frame.Controls) (address : Address)
    (first : flags.1 = nextFlags.1) (second : flags.2.2 = nextFlags.2.2)
    (index : Fin (width + 1)) :
    (Enable.digitBit stream width bounded index).get
        (clearedInitial input numerator flags address) =
      (Enable.digitBit stream width bounded index).get
        (clearedInitial nextInput nextNumerator nextFlags address) := by
  refine Fin.cases ?_ (fun digit => ?_) index
  · change (streamBit stream).get _ = (streamBit stream).get _
    unfold streamBit
    split
    · change (clearedInitial input numerator flags address).1.2.1 =
        (clearedInitial nextInput nextNumerator nextFlags address).1.2.1
      rw [clearedInitial_flags, clearedInitial_flags]
      exact first
    · change (clearedInitial input numerator flags address).1.2.2.2 =
        (clearedInitial nextInput nextNumerator nextFlags address).1.2.2.2
      rw [clearedInitial_flags, clearedInitial_flags]
      exact second
  · change (addressBit ⟨digit.val, lt_of_lt_of_le digit.isLt bounded⟩).get _ =
      (addressBit ⟨digit.val, lt_of_lt_of_le digit.isLt bounded⟩).get _
    simp only [addressBit_get, clearedInitial]

/-- Arbitrary binary X and Y replacements retain the same full original table row. -/
lemma selectedRow_clearedInitial_values (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator nextInput nextNumerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Address) :
    selectedRow stream width bounded (clearedInitial input numerator flags address) =
      selectedRow stream width bounded
        (clearedInitial nextInput nextNumerator flags address) :=
  selectedRow_eq_of_digit stream width bounded _ _
    (initializer_digit_congr stream width bounded input numerator nextInput nextNumerator
      flags flags address rfl rfl)

/-- Changing only genuine N preserves the original top-plus-address row for every width. -/
lemma selectedRow_clearedInitial_setNormal (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (value : Bool) (address : Address) :
    selectedRow stream width bounded
        (clearedInitial input numerator (setNormal flags value) address) =
      selectedRow stream width bounded (clearedInitial input numerator flags address) :=
  selectedRow_eq_of_digit stream width bounded _ _
    (initializer_digit_congr stream width bounded input numerator input numerator
      (setNormal flags value) flags address rfl rfl)

/-- Every mathematical field column reads the same row after arbitrary binary X/Y changes. -/
lemma selectedFieldColumn_clearedInitial_values (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator nextInput nextNumerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Address) (column : Fin 5) :
    selectedFieldColumn curve point stream width bounded
        (clearedInitial input numerator flags address) column =
      selectedFieldColumn curve point stream width bounded
        (clearedInitial nextInput nextNumerator flags address) column :=
  congrArg (fun row : Fin (2 ^ (width + 1)) =>
    ((pointFiveColumns curve (row.val • point) column).val : ZMod modulus))
      (selectedRow_clearedInitial_values stream width bounded input numerator
        nextInput nextNumerator flags address)

/-- The same original field column is independent of the genuine normal flag. -/
lemma selectedFieldColumn_clearedInitial_setNormal (curve : CurveSpec 256)
    (point : ClassicalAlgorithms.EllipticCurve.Point curve)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (value : Bool) (address : Address) (column : Fin 5) :
    selectedFieldColumn curve point stream width bounded
        (clearedInitial input numerator (setNormal flags value) address) column =
      selectedFieldColumn curve point stream width bounded
        (clearedInitial input numerator flags address) column :=
  congrArg (fun row : Fin (2 ^ (width + 1)) =>
    ((pointFiveColumns curve (row.val • point) column).val : ZMod modulus))
      (selectedRow_clearedInitial_setNormal stream width bounded input numerator
        flags value address)

end

end Tables

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
