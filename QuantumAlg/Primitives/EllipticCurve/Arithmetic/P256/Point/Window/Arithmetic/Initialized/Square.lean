/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Initialized
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Arithmetic.Square.Field

/-!
# Actual square subtraction returns the complete updated initialized label

Only the real whole-digit enable controls X minus Y squared. The same
native copy, inverse MAC and uncopy restore A and the three arithmetic
flags. F remains live, while original padding, small history, C/N/W and
the full address are retained in the exact output initializer.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace Initialized

noncomputable section

open Chain.Arithmetic.Call Chain.Arithmetic.Call.Endpoint

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus inputState ket

/-- No whole-pool clean premise is imposed while the actual enable is live. -/
lemma subtractSquareProgram_inputState (environment : OracleModel.empty.Interpretation)
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Address) :
    (suffixProgram Native.BorrowedControl.subtractSquareProgram).applyNormalized environment
        (ket (inputState stream width bounded (Residue.input x) (Residue.input y) flags address)) =
      ket (inputState stream width bounded
        (Residue.input
          (if divisionEnabled stream width bounded (Residue.input x) (Residue.input y)
            flags address then x - y ^ 2 else x))
        (Residue.input y) flags address) := by
  have actual := subtractSquareProgram_field_label environment
    (inputState stream width bounded (Residue.input x) (Residue.input y) flags address)
    (inputState_arithmeticFlags Native.squarePorts stream width bounded
      (Residue.input x) (Residue.input y) flags address)
    (inputState_work1 stream width bounded (Residue.input x) (Residue.input y) flags address)
    y x (inputState_field_numerator stream width bounded x y flags address)
    (inputState_field_work2 stream width bounded x y flags address)
  rw [inputState_flag] at actual
  exact actual.trans (congrArg ket
    (inputState_setWork2_residue stream width bounded x y _ flags address))

end

end Initialized

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
