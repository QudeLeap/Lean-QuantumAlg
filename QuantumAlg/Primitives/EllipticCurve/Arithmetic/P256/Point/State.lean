/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Correctness

/-!
# Original state coverage and complete retained-coordinate restoration

The arithmetic coordinate labels cover every original state whose three
borrowed flags are zero. A clean scan pool is one sufficient caller
condition. Every unselected original coordinate has its original value;
the word padding, remaining pool, history and C/N/W are included.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

lemma arithmeticState_source (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) :
    ports.source.value (arithmeticState ports source target multiplier retained) = source := by
  have actual := Placement.grouping_source ports
    (arithmeticState ports source target multiplier retained)
  rw [arithmeticState_grouping] at actual
  exact actual.symm

lemma arithmeticState_target (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) :
    ports.target.value (arithmeticState ports source target multiplier retained) = target := by
  have actual := Placement.grouping_target ports
    (arithmeticState ports source target multiplier retained)
  rw [arithmeticState_grouping] at actual
  exact actual.symm

lemma arithmeticState_multiplier (ports : PortAssignment) (source target multiplier : Word)
    (retained : Placement.Rest ports) :
    ports.multiplier.value (arithmeticState ports source target multiplier retained) =
      multiplier := by
  have actual := Placement.grouping_multiplier ports
    (arithmeticState ports source target multiplier retained)
  rw [arithmeticState_grouping] at actual
  exact actual.symm

/-- Exactly the three actual selected flags suffice; the other original bits are arbitrary. -/
lemma state_eq_arithmeticState_of_flags (ports : PortAssignment) (state : Frame.Raw)
    (flags : ((Placement.layout ports).grouping state).1.1.2 = false ∧
      ((Placement.layout ports).grouping state).1.2.1 = false ∧
        ((Placement.layout ports).grouping state).1.2.2 = false) :
    state = arithmeticState ports (ports.source.value state) (ports.target.value state)
      (ports.multiplier.value state) ((Placement.layout ports).grouping state).2.2 := by
  apply (Placement.layout ports).grouping.injective
  refine Eq.trans ?_ (arithmeticState_grouping ports (ports.source.value state)
    (ports.target.value state) (ports.multiplier.value state)
      ((Placement.layout ports).grouping state).2.2).symm
  apply Prod.ext
  · apply Prod.ext
    · exact Prod.ext (Prod.ext (Placement.grouping_source ports state)
        (Placement.grouping_target ports state)) flags.1
    · exact Prod.ext flags.2.1 flags.2.2
  · exact Prod.ext (Placement.grouping_multiplier ports state) rfl

/-- A caller's genuinely initialized pool supplies the three flags at their original positions. -/
lemma state_eq_arithmeticState (ports : PortAssignment) (state : Frame.Raw)
    (clean : Frame.CleanPool state) :
    state = arithmeticState ports (ports.source.value state) (ports.target.value state)
      (ports.multiplier.value state) ((Placement.layout ports).grouping state).2.2 :=
  state_eq_arithmeticState_of_flags ports state (Placement.grouping_flags_clean ports state clean)

lemma arithmeticState_restBit (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range (Placement.subsystem ports).wires)
    (source target multiplier : Word) (retained : Placement.Rest ports) :
    bit.get (arithmeticState ports source target multiplier retained) =
      (Placement.restBit ports bit outside).get retained := by
  have actual := Placement.restBit_get ports bit outside
    (arithmeticState ports source target multiplier retained)
  rw [arithmeticState_grouping] at actual
  exact actual.symm

/-- Equality of the entire retained component restores every original complementary bit. -/
lemma arithmeticState_complement (ports : PortAssignment) (bit : EncodedBit Frame.encoding)
    (outside : bit.wire ∉ Set.range (Placement.subsystem ports).wires)
    (source target multiplier newSource newTarget newMultiplier : Word)
    (retained : Placement.Rest ports) :
    bit.get (arithmeticState ports newSource newTarget newMultiplier retained) =
      bit.get (arithmeticState ports source target multiplier retained) :=
  (arithmeticState_restBit ports bit outside newSource newTarget newMultiplier retained).trans
    (arithmeticState_restBit ports bit outside source target multiplier retained).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
