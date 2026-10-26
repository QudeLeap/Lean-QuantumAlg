/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Reflect

/-!
# Actual reflection returns the complete updated initialized label

The real retained-enable reflection changes the original X to minus
one minus X on the selected sector. The same original A is restored,
and the exact output initializer retains Y, padding, small history,
the live pool, C/N/W and the complete address.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialized

noncomputable section

open Chain.Arithmetic.Call Chain.Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState ket

lemma reflectionProgram_inputState (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Address) :
    (suffixProgram Chain.Arithmetic.Reflect.program).applyNormalized environment
        (ket (inputState stream width bounded (Residue.input x) (Residue.input y) flags address)) =
      ket (inputState stream width bounded
        (Residue.input
          (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
            flags address then -1 - x else x))
        (Residue.input y) flags address) := by
  have zero : Frame.work1
      (inputState stream width bounded (Residue.input x) (Residue.input y) flags address).1 =
        MAU.Addition.TTK.Reflection.zero 256 :=
    inputState_work1 stream width bounded (Residue.input x) (Residue.input y) flags address
  have actual := reflectionProgram_field_label environment
    (inputState stream width bounded (Residue.input x) (Residue.input y) flags address) zero x
    (inputState_field_work2 stream width bounded x y flags address)
  rw [inputState_flag] at actual
  exact actual.trans (congrArg ket
    (inputState_setWork2_residue stream width bounded x y _ flags address))

end

end Initialized

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
