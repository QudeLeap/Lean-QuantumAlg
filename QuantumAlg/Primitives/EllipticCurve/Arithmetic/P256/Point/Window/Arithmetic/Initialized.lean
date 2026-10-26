/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Normal.Initializer
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.WordUpdate.Input
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Input

/-!
# Original field words and arithmetic flags on the live-enable initialized label

The three arithmetic flags are read through their actual placed ports.
Their cleanliness does not require the whole pool to be zero: the real
enable at F560 remains live. The field-word setter is the complete
original initializer equality, including its three padding positions
and all other source, pool, C/N/W and address coordinates.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialized

noncomputable section

open EncodedBit.WindowLookup Chain.Arithmetic.Call Chain.Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus

/-- The actual retained F is the same whole-digit enable used by the original call. -/
lemma inputState_flag (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address) :
    Native.BorrowedControl.flag.get
        (inputState stream width bounded input numerator flags address).1 =
      divisionEnabled stream width bounded input numerator flags address :=
  (Chain.Control.flag_get _).symm.trans
    (Chain.Normal.inputState_flag stream width bounded input numerator flags address)

/-- Every actual original port assignment reads the same three clean arithmetic systems. -/
lemma inputState_arithmeticFlags (ports : PortAssignment)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Address) :
    ((Placement.layout ports).grouping
      (inputState stream width bounded input numerator flags address).1).1.1.2 = false ∧
      ((Placement.layout ports).grouping
        (inputState stream width bounded input numerator flags address).1).1.2.1 = false ∧
      ((Placement.layout ports).grouping
        (inputState stream width bounded input numerator flags address).1).1.2.2 = false := by
  let state := (inputState stream width bounded input numerator flags address).1
  have original := inputState_flags stream width bounded input numerator flags address
  have physical (index : Fin 3) : (arithmeticFlag index).get state = false := by
    fin_cases index
    · exact (Placement.arithmeticFlagPort_get Chain.Arithmetic.Save.ports
        ⟨0, by decide⟩ state).symm.trans original.1
    · exact (Placement.arithmeticFlagPort_get Chain.Arithmetic.Save.ports
        ⟨1, by decide⟩ state).symm.trans original.2.1
    · exact (Placement.arithmeticFlagPort_get Chain.Arithmetic.Save.ports
        ⟨2, by decide⟩ state).symm.trans original.2.2
  exact ⟨(Placement.arithmeticFlagPort_get ports ⟨0, by decide⟩ state).trans (physical 0),
    (Placement.arithmeticFlagPort_get ports ⟨1, by decide⟩ state).trans (physical 1),
    (Placement.arithmeticFlagPort_get ports ⟨2, by decide⟩ state).trans (physical 2)⟩

lemma inputState_field_work2 (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Address) :
    Frame.work2
        (inputState stream width bounded (Residue.input x) (Residue.input y) flags address).1 =
      Residue.word x :=
  (inputState_work2 stream width bounded (Residue.input x) (Residue.input y) flags address).trans
    (Residue.cast_input x)

lemma inputState_field_numerator (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Address) :
    Frame.numerator
        (inputState stream width bounded (Residue.input x) (Residue.input y) flags address).1 =
      Residue.word y :=
  (inputState_numerator stream width bounded (Residue.input x) (Residue.input y)
    flags address).trans (Residue.cast_input y)

/-- The actual original X-word setter is the same complete initializer at the updated value. -/
lemma inputState_setWork2_residue (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y updated : ZMod modulus) (flags : Frame.Controls) (address : Address) :
    resultSetConstant (resultWord .work2) (Residue.word updated)
        (inputState stream width bounded (Residue.input x) (Residue.input y) flags address) =
      inputState stream width bounded (Residue.input updated) (Residue.input y) flags address := by
  have actual := inputState_setWork2 stream width bounded (Residue.input x)
    (Residue.input updated) (Residue.input y) flags address
  rw [Residue.cast_input] at actual
  exact actual

end

end Initialized

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
