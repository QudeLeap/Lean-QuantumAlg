/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Reset
import all QuantumAlg.Components.Encoded.BitGates.StateEquality

/-! # Complete physical readouts of the actual reset branch label -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset

noncomputable section

open EncodedBit.WindowLookup

/-- The same physical word has exactly the named branch value, in its original numerical order. -/
lemma namedOutcome_value (port : WordPort) (value : Fin (2 ^ 256)) (state : Window.Raw) :
    port.value (namedOutcome port value state).1 = value := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  have read := resultSetConstant_get (Window.resultWord port) (Window.resultWord_distinct port)
    value state index
  change (Window.pointBit (port.bit index)).get (namedOutcome port value state) = _ at read
  simpa only [Window.pointBit_get, WordPort.bit_get] using read

/-- Every physical bit outside the measured word retains its complete original value. -/
lemma namedOutcome_other (port : WordPort) (value : Fin (2 ^ 256))
    (observed : EncodedBit Window.encoding)
    (outside : ∀ index, ((Window.resultWord port).bit index).wire ≠ observed.wire)
    (state : Window.Raw) :
    observed.get (namedOutcome port value state) = observed.get state :=
  resultSetConstant_observed (Window.resultWord port) value observed outside state

/-- All original source, padding, history and pool positions lie outside the physical Y bank. -/
lemma namedOutcome_numerator_outside (value : Fin (2 ^ 256))
    (observed : EncodedBit Window.encoding)
    (outside : observed.wire.val < 580 ∨ 836 ≤ observed.wire.val) (state : Window.Raw) :
    observed.get (namedOutcome .numerator value state) = observed.get state := by
  apply namedOutcome_other .numerator value observed
  intro index same
  have positions := congrArg Fin.val same
  rw [Window.resultWord_wire] at positions
  change 580 + (255 - index.val) = observed.wire.val at positions
  omega

/-- Physical reset of Y retains the entire original source and all twenty-one pool systems. -/
lemma namedOutcome_numerator_scan (value : Fin (2 ^ 256)) (state : Window.Raw) :
    (namedOutcome .numerator value state).1.1.1 = state.1.1.1 := by
  apply EncodedBit.state_eq_of_get_eq (MAU.Inversion.SharedEEA.Scanned.encoding_surjective 256)
  intro observed
  have below : (Window.pointBit (Frame.scanBit observed)).wire.val < 580 := by
    rw [Window.pointBit_wire, Frame.scanBit_wire]
    calc
      observed.wire.val < (MAU.Inversion.SharedEEA.Scanned.encoding 256).width :=
        observed.wire.isLt
      _ = 580 := MAU.Inversion.SharedEEA.Scanned.p256_encoding_width
  have read := namedOutcome_numerator_outside value
    (Window.pointBit (Frame.scanBit observed)) (Or.inl below) state
  simpa only [Window.pointBit_get, Frame.scanBit_get] using read

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Reset
