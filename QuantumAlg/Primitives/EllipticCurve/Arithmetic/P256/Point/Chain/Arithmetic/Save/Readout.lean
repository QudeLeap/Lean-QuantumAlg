/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Save.Boundary
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Placement
import all QuantumAlg.Components.Encoded.BitGates.BitEquality

/-!
# Complete retained physical readouts of the actual product save

The three arithmetic flags are explicitly zero on both sides. Source and
multiplier coordinates retain their actual words; every remaining coordinate
comes from the same complete placement complement. Thus no original small
history is inferred solely from the numerical word values.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Save

noncomputable section

private lemma flag_zero (assignment : PortAssignment) (index : Fin 3) (state : Frame.Raw)
    (flags : ((Placement.layout assignment).grouping state).1.1.2 = false ∧
      ((Placement.layout assignment).grouping state).1.2.1 = false ∧
        ((Placement.layout assignment).grouping state).1.2.2 = false) :
    (arithmeticFlag index).get state = false := by
  fin_cases index
  · exact (Placement.arithmeticFlagPort_get assignment ⟨0, by decide⟩ state).symm.trans flags.1
  · exact (Placement.arithmeticFlagPort_get assignment ⟨1, by decide⟩ state).symm.trans flags.2.1
  · exact (Placement.arithmeticFlagPort_get assignment ⟨2, by decide⟩ state).symm.trans flags.2.2

lemma savedState_flags (assignment : PortAssignment) (selection : Selector) (state : Frame.Raw) :
    ((Placement.layout assignment).grouping (savedState assignment selection state)).1.1.2 = false ∧
      ((Placement.layout assignment).grouping
        (savedState assignment selection state)).1.2.1 = false ∧
        ((Placement.layout assignment).grouping
          (savedState assignment selection state)).1.2.2 = false := by
  have actual := Native.arithmeticState_grouping assignment (assignment.source.value state)
    (savedWord (assignment.source.value state) (assignment.multiplier.value state)
      ((selectorBit assignment selection).get ((Placement.layout assignment).grouping state).2.2))
    (assignment.multiplier.value state) ((Placement.layout assignment).grouping state).2.2
  exact ⟨congrArg (fun value : Horner.OperandRegisters (Word × Placement.Rest assignment) =>
    value.1.1.2) actual,
    congrArg (fun value : Horner.OperandRegisters (Word × Placement.Rest assignment) =>
      value.1.2.1) actual,
    congrArg (fun value : Horner.OperandRegisters (Word × Placement.Rest assignment) =>
      value.1.2.2) actual⟩

/-- Only the target payload changes; all other original physical coordinates are retained. -/
lemma savedState_other (assignment : PortAssignment) (selection : Selector)
    (observed : EncodedBit Frame.encoding)
    (outsideTarget : ∀ index, (assignment.target.bit index).wire ≠ observed.wire)
    (state : Frame.Raw)
    (flags : ((Placement.layout assignment).grouping state).1.1.2 = false ∧
      ((Placement.layout assignment).grouping state).1.2.1 = false ∧
        ((Placement.layout assignment).grouping state).1.2.2 = false) :
    observed.get (savedState assignment selection state) = observed.get state := by
  classical
  by_cases outside : observed.wire ∉ Set.range (Placement.subsystem assignment).wires
  · exact savedState_complement assignment selection observed outside state
  · obtain ⟨index, same⟩ := Classical.not_not.mp outside
    change Placement.pickPosition assignment (Placement.prefixPicks index) = observed.wire at same
    generalize Placement.prefixPicks index = picked at same
    rcases picked with ((source | target) | flag) | multiplier
    · change (assignment.source.bit source.rev).wire = observed.wire at same
      rw [← EncodedBit.eq_of_wire_eq _ observed same, WordPort.bit_get,
        savedState_source, ← WordPort.bit_get]
    · change (assignment.target.bit target.rev).wire = observed.wire at same
      exact False.elim (outsideTarget target.rev same)
    · change (arithmeticFlag flag).wire = observed.wire at same
      rw [← EncodedBit.eq_of_wire_eq _ observed same]
      exact (flag_zero assignment flag _ (savedState_flags assignment selection state)).trans
        (flag_zero assignment flag state flags).symm
    · change (assignment.multiplier.bit multiplier.rev).wire = observed.wire at same
      rw [← EncodedBit.eq_of_wire_eq _ observed same, WordPort.bit_get,
        savedState_multiplier, ← WordPort.bit_get]

end

end Arithmetic.Save

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
