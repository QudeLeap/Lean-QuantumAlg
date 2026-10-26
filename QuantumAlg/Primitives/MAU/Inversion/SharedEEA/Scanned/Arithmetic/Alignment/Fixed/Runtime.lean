/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Range
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Fixed.Readout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Preservation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Alignment.Pair
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# The actual paid quantum-metadata barrel has the complete static frame action

The actual emitted program is independent of the quantum input. A
public displacement is used only to state the full output equality
on source labels having that metadata. Both full work words, every
original saved bit, and the whole physical pool are covered.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed

noncomputable section

open EncodedBit

/-- Every physical output of the same actual barrel equals its complete declared coordinates. -/
lemma pairGates_eq_frame (width displacement : Nat) (field : ArithmeticGeometry.Field)
    (state : Data width)
    (metadata : (ArithmeticGeometry.fieldValue field state).toNat = displacement) :
    GateSpec.stepList (pairGates width field) state =
      (frame width displacement).grouping state := by
  apply state_eq_of_get_eq (Scanned.encoding_surjective width)
  intro observed
  by_cases inside : observed.wire ∈ Set.range (operands width).wires
  · obtain ⟨index, location⟩ := inside
    revert location
    refine Fin.addCases (m := width + 3) (n := width + 3)
      (fun first location => ?_) (fun second location => ?_) index
    · change (wordPairSubsystem _ _ _ _ _).wires
        (Fin.castAdd (width + 3) first) = observed.wire at location
      rw [wordPairSubsystem_left] at location
      have lenses := eq_of_wire_eq (ArithmeticRotation.bit width true first) observed location
      rw [← lenses]
      have actual := pairGates_bit_get width field true first state
      rw [metadata] at actual
      exact actual.trans (frame_word_get width displacement true first state).symm
    · change (wordPairSubsystem _ _ _ _ _).wires
        (Fin.natAdd (width + 3) second) = observed.wire at location
      rw [wordPairSubsystem_right] at location
      have lenses := eq_of_wire_eq (ArithmeticRotation.bit width false second) observed location
      rw [← lenses]
      have actual := pairGates_bit_get width field false second state
      rw [metadata] at actual
      exact actual.trans (frame_word_get width displacement false second state).symm
  · have outside : 2 * (width + 3) ≤ observed.wire.val := by
      by_contra below
      exact inside ((operands_range_iff width observed.wire).mpr (by omega))
    exact (pairGates_get_retained width field observed outside state).trans
      (frame_other_get width displacement observed inside state).symm

/-- The actual fixed native unitary realizes these same complete coordinates on each such ket. -/
lemma pairProgram_apply_frame (width displacement : Nat) (field : ArithmeticGeometry.Field)
    (environment : OracleModel.empty.Interpretation) (state : Data width)
    (metadata : (ArithmeticGeometry.fieldValue field state).toNat = displacement) :
    (pairProgram width field).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode ((frame width displacement).grouping state))) := by
  have actual := (pairProgram_realizes width field environment).apply_encoded_ket state
  exact actual.trans (congrArg
    (fun value : Data width => NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
      ((encoding width).encode value)))
    (pairGates_eq_frame width displacement field state metadata))

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticAlignment.Fixed
