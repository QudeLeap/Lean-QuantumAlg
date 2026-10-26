/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Division.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Field.Domain

/-!
# Ordinary field quotient of the same complete measured division label

The original enable decides whether the returned Y is y/x or the original
y. The original arithmetic domain is used only in that selected sector.
The complete-label equality keeps the source, padding and every genuine
selector, rather than equating only the two numerical readouts.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

attribute [local implicit_reducible] capacity width

attribute [local irreducible] modulus inputState divisionOutput divisionNumerator

/-- The original numerical division output represents precisely the selected field quotient. -/
lemma divisionNumerator_residue [Fact modulus.Prime]
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address)
    (admitted : divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
      flags address = true → ActiveDomain (Residue.input x) (Residue.input y)) :
    divisionNumerator stream width bounded (Residue.input x) (Residue.input y) flags address
        admitted =
      Residue.word (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
        flags address then y / x else y) := by
  by_cases selected : divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
      flags address = true
  · rw [divisionNumerator_selected stream width bounded (Residue.input x) (Residue.input y)
        flags address admitted selected, if_pos selected, Residue.cast_input,
      Residue.saved_division_word _ (admitted selected).coprime
        (admitted selected).positive (admitted selected).bounded,
      Residue.input_cast]
  · rw [divisionNumerator_disabled stream width bounded (Residue.input x) (Residue.input y)
        flags address admitted selected, if_neg selected, inputState_numerator, Residue.cast_input]

/-- The same actual division changes only Y to the selected field quotient. -/
lemma divisionOutput_residue [Fact modulus.Prime]
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (normalZero : flags.2.1 = false)
    (address : Window.Address)
    (admitted : divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
      flags address = true → ActiveDomain (Residue.input x) (Residue.input y)) :
    divisionOutput stream width bounded (Residue.input x) (Residue.input y) flags address
        admitted =
      withNumerator
        (inputState stream width bounded (Residue.input x) (Residue.input y) flags address)
        (Residue.word (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
          flags address then y / x else y)) := by
  rw [divisionOutput_eq stream width bounded _ _ flags normalZero address admitted,
    divisionNumerator_residue]

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
