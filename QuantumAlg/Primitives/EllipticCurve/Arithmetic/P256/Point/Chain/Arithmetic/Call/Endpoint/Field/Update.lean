/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Field
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Field.Division
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate

/-!
# Both actual field calls return the complete next initialized label

The complete original output, not merely its Y readout, is the same
initializer with the updated ordinary field numerator. The real following
enable toggle therefore returns precisely the next cleared initializer.
All original padding, source metadata, C/N/W and address are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

attribute [local implicit_reducible] capacity width

attribute [local irreducible] modulus inputState divisionOutput multiplicationOutput

/-- The complete actual multiplication output is the same next live-F initializer. -/
lemma multiplicationOutput_inputState_residue
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    multiplicationOutput stream width bounded (Residue.input x) (Residue.input y) flags address =
      inputState stream width bounded (Residue.input x)
        (Residue.input (if flags.2.1 then y * x else y)) flags address := by
  rw [multiplicationOutput_residue]
  have actual := inputState_setNumerator stream width bounded (Residue.input x) (Residue.input y)
    (Residue.input (if flags.2.1 then y * x else y)) flags address
  rw [Residue.cast_input, resultSetConstant_withNumerator] at actual
  exact actual

/-- The actual subsequent enable clearing restores the complete updated multiplication source. -/
lemma multiplicationOutput_clear_residue
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    Window.Enable.step stream width bounded
        (multiplicationOutput stream width bounded (Residue.input x) (Residue.input y)
          flags address) =
      clearedInitial (Residue.input x) (Residue.input (if flags.2.1 then y * x else y))
        flags address := by
  rw [multiplicationOutput_inputState_residue, inputState_clear]

/-- The complete actual division output is the same next live-F initializer. -/
lemma divisionOutput_inputState_residue [Fact modulus.Prime]
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (normalZero : flags.2.1 = false)
    (address : Window.Address)
    (admitted : divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
      flags address = true → ActiveDomain (Residue.input x) (Residue.input y)) :
    divisionOutput stream width bounded (Residue.input x) (Residue.input y) flags address
        admitted =
      inputState stream width bounded (Residue.input x)
        (Residue.input
          (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
            flags address then y / x else y)) flags address := by
  rw [divisionOutput_residue stream width bounded x y flags normalZero address admitted]
  have actual := inputState_setNumerator stream width bounded (Residue.input x) (Residue.input y)
    (Residue.input
      (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
        flags address then y / x else y)) flags address
  rw [Residue.cast_input, resultSetConstant_withNumerator] at actual
  exact actual

/-- The real enable clearing restores the complete updated division source. -/
lemma divisionOutput_clear_residue [Fact modulus.Prime]
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (normalZero : flags.2.1 = false)
    (address : Window.Address)
    (admitted : divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
      flags address = true → ActiveDomain (Residue.input x) (Residue.input y)) :
    Window.Enable.step stream width bounded
        (divisionOutput stream width bounded (Residue.input x) (Residue.input y)
          flags address admitted) =
      clearedInitial (Residue.input x)
        (Residue.input
          (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
            flags address then y / x else y)) flags address := by
  rw [divisionOutput_inputState_residue stream width bounded x y flags normalZero address admitted,
    inputState_clear]

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
