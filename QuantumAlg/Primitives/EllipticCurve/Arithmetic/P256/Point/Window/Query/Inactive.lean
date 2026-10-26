/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Effect

/-!
# Full original-label identity for an actually disabled query target

The inactive target word is arbitrary binary data. Its exact original
readouts prove that the same mathematical setter is identity on the
complete physical label, without canonicality or a field interpretation.
The ordinary and exceptional queries share the same all-zero digit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

namespace QueryInsertion

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus

/-- A zero original digit disables both actual selector kinds for every original N value. -/
lemma querySelected_zero (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (exceptional : Bool) (state : Raw)
    (zero : ∀ index, (Enable.digitBit stream width bounded index).get state = false) :
    querySelected stream width bounded exceptional state = false := by
  have decision :
      decide (∀ index, (Enable.digitBit stream width bounded index).get state = false) = true :=
    decide_eq_true_eq.mpr zero
  unfold querySelected
  rw [decision]
  cases exceptional <;> rfl

/-- The original target setter is exact identity on every disabled binary label. -/
lemma queryValue_disabled_label (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (ports : PortAssignment) (exceptional : Bool)
    (table : Bool → Fin (2 ^ width) → Fin (2 ^ 256)) (state : Raw)
    (disabled : querySelected stream width bounded exceptional state = false) :
    resultSetConstant (resultWord ports.target)
        (queryValue stream width bounded ports exceptional table state) state = state := by
  rw [queryValue, disabled, if_neg Bool.false_ne_true]
  apply resultSetConstant_self encoding_surjective (resultWord ports.target)
    (resultWord_distinct ports.target)
  intro index
  exact WordPort.bit_get ports.target index state.1

end

end QueryInsertion

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
