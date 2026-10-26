/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Readout
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Residue.Input

/-!
# Ordinary field output of the same complete measured multiplication label

The numerical interpretation changes no program, outcome or coefficient.
It rewrites the existing exact output label and retains the whole source,
pool, padding, genuine selectors and original address.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

attribute [local implicit_reducible] capacity width

attribute [local irreducible] modulus inputState multiplicationOutput

/-- Both genuine-N sectors have the same original ordinary field-coordinate output. -/
lemma multiplicationOutput_residue (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    multiplicationOutput stream width bounded (Residue.input x) (Residue.input y) flags address =
      withNumerator
        (inputState stream width bounded (Residue.input x) (Residue.input y) flags address)
        (Residue.word (if flags.2.1 then y * x else y)) := by
  rw [multiplicationOutput_eq, inputState_work2, inputState_numerator,
    Residue.cast_input, Residue.cast_input, Residue.saved_word]

/-- The actual output's original Y word is this same ordinary field value. -/
lemma multiplicationOutput_numerator_residue
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (x y : ZMod modulus) (flags : Frame.Controls) (address : Window.Address) :
    Frame.numerator
        (multiplicationOutput stream width bounded (Residue.input x) (Residue.input y)
          flags address).1 = Residue.word (if flags.2.1 then y * x else y) := by
  rw [multiplicationOutput_numerator, Residue.cast_input, Residue.cast_input, Residue.saved_word]

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
