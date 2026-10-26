/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Retained readouts through the actual complete enable toggle

The real toggle changes only its output bit according to the original
digit. Equal digit reads and equal observed input reads therefore give
equal observed output reads, including when the observed bit is the
toggle output. This rule applies before the concrete16/4-control choices.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open EncodedBit

lemma toggleStep_get_congr {Data : Type} {encoding : BinaryLabelEncoding Data}
    {controls : Nat} (ports : Word.OneDirtyLayout (encoding := encoding) controls)
    (observed : EncodedBit encoding) (first second : Data)
    (digit : ∀ index, (ports.source.bit index).get first =
      (ports.source.bit index).get second)
    (read : observed.get first = observed.get second) :
    observed.get (toggleStep ports first) = observed.get (toggleStep ports second) := by
  by_cases same : ports.output.wire = observed.wire
  · have sameBit : observed = ports.output := eq_of_wire_eq _ _ same.symm
    rw [sameBit] at read ⊢
    rw [toggleStep_output, toggleStep_output, read]
    have zero : (∀ index, (ports.source.bit index).get first = false) ↔
        ∀ index, (ports.source.bit index).get second = false := by
      constructor
      · intro all index
        exact (digit index).symm.trans (all index)
      · intro all index
        exact (digit index).trans (all index)
    simp only [zero]
  · rw [toggleStep_other ports observed same, toggleStep_other ports observed same, read]

/-- The original whole-digit enable preserves equal complete readouts on either input. -/
lemma step_get_congr (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (observed : EncodedBit Window.encoding) (first second : Raw)
    (digit : ∀ index, (digitBit stream width bounded index).get first =
      (digitBit stream width bounded index).get second)
    (read : observed.get first = observed.get second) :
    observed.get (step stream width bounded first) =
      observed.get (step stream width bounded second) :=
  toggleStep_get_congr (layout stream width bounded) observed first second digit read

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
