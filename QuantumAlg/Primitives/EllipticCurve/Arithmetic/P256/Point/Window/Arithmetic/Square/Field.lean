/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Square
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Arithmetic

/-!
# Ordinary field value of the actual whole-window square subtraction

The exact finite-word result of the original copy/inverse-MAC/uncopy
is the ordinary residue of X-Y squared on the real enabled sectors.
Its complete original-label setter keeps every other source and address
coordinate, using the same already counted native program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

/-- The actual numerical result is the same ordinary field difference on the original real F. -/
lemma square_difference_word (state : Frame.Raw) (source target : ZMod modulus)
    (sourceValue : Frame.numerator state = Residue.word source)
    (targetValue : Frame.work2 state = Residue.word target) :
    Accumulate.Inverse.differenceWord (Frame.numerator state) (Frame.numerator state)
        (Frame.work2 state) ((Native.BorrowedControl.controlBit Native.squarePorts).get
          ((Placement.layout Native.squarePorts).grouping state).2.2) =
      Residue.word
        (if Native.BorrowedControl.flag.get state then target - source ^ 2 else target) := by
  rw [sourceValue, targetValue, Native.BorrowedControl.controlBit_get]
  cases Native.BorrowedControl.flag.get state with
  | false => rfl
  | true => simpa only [pow_two, if_true] using Residue.difference_word source source target

/-- The unchanged complete native window program realizes that ordinary field operation. -/
lemma subtractSquareProgram_field_label (environment : OracleModel.empty.Interpretation)
    (state : Raw)
    (flags : ((Placement.layout Native.squarePorts).grouping state.1).1.1.2 = false ∧
      ((Placement.layout Native.squarePorts).grouping state.1).1.2.1 = false ∧
        ((Placement.layout Native.squarePorts).grouping state.1).1.2.2 = false)
    (zero : Frame.work1 state.1 = Horner.zeroWord)
    (source target : ZMod modulus)
    (sourceValue : Frame.numerator state.1 = Residue.word source)
    (targetValue : Frame.work2 state.1 = Residue.word target) :
    (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
        (ket state) =
      ket (resultSetConstant (resultWord .work2)
        (Residue.word
          (if Native.BorrowedControl.flag.get state.1 then target - source ^ 2 else target))
        state) := by
  have sourceAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.numerator state.1) := by
    intro _
    rw [sourceValue]
    exact Residue.word_canonical source
  have targetAdmitted : (Native.BorrowedControl.controlBit Native.squarePorts).get
      ((Placement.layout Native.squarePorts).grouping state.1).2.2 = true →
        Canonical (Frame.work2 state.1) := by
    intro _
    rw [targetValue]
    exact Residue.word_canonical target
  have actual := subtractSquareProgram_original_label environment state flags zero
    sourceAdmitted targetAdmitted
  rw [square_difference_word state.1 source target sourceValue targetValue] at actual
  exact actual

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
