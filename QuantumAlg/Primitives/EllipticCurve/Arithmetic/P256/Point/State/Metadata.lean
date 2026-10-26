/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Complete original metadata across native arithmetic-coordinate updates

All three numerical words are selected by their real physical ports.
The three selected flags have the specified zero values, and every other
original coordinate comes from the identical retained component. Thus
changing numerical word values preserves every nonword coordinate. This
includes the complete scan pool, history, padding and coherent controls.
No physical circuit or additional cleanliness promise is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

open EncodedBit

/-- The complete arithmetic coordinates contain the three original zero flags. -/
lemma arithmeticState_flag (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) (index : Fin 3) :
    (arithmeticFlag index).get (arithmeticState ports source target multiplier retained) =
      false := by
  have actual := Placement.arithmeticFlagPort_get ports index
    (arithmeticState ports source target multiplier retained)
  rw [arithmeticState_grouping] at actual
  fin_cases index <;> exact actual.symm

/-- Every original nonword bit is retained when only numerical coordinates change. -/
lemma arithmeticState_nonword (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (nonword : ∀ port index, bit.wire ≠ (WordPort.bit port index).wire)
    (source target multiplier newSource newTarget newMultiplier : Word)
    (retained : Placement.Rest ports) :
    bit.get (arithmeticState ports newSource newTarget newMultiplier retained) =
      bit.get (arithmeticState ports source target multiplier retained) := by
  by_cases selected : ∃ index, bit.wire = (arithmeticFlag index).wire
  · obtain ⟨index, same⟩ := selected
    rw [eq_of_wire_eq bit (arithmeticFlag index) same, arithmeticState_flag,
      arithmeticState_flag]
  · have outside : bit.wire ∉ Set.range (Placement.subsystem ports).wires := by
      rintro ⟨index, same⟩
      change Placement.pickPosition ports (Placement.prefixPicks index) = bit.wire at same
      rcases value : Placement.prefixPicks index with ((first | second) | flag) | third
      · rw [value] at same
        exact nonword ports.source first.rev same.symm
      · rw [value] at same
        exact nonword ports.target second.rev same.symm
      · rw [value] at same
        exact selected ⟨flag, same.symm⟩
      · rw [value] at same
        exact nonword ports.multiplier third.rev same.symm
    exact arithmeticState_complement ports bit outside source target multiplier
      newSource newTarget newMultiplier retained

/-- A real wire in the original scan pool is outside all three numerical words. -/
lemma pool_wire_nonword (bit : EncodedBit Frame.encoding)
    (lower : 559 ≤ bit.wire.val) (upper : bit.wire.val < 580)
    (port : WordPort) (index : Fin 256) : bit.wire ≠ (port.bit index).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [WordPort.bit_wire] at positions
  have within := index.isLt
  cases port <;> simp only [WordPort.physicalIndex] at positions <;> omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
