/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.State.Metadata
import all QuantumAlg.Components.Encoded.BitGates.StateEquality
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Fiber

/-!
# Complete native target-word replacement in the original arithmetic coordinates

The same retained component fixes every original position outside the
selected target. Replacing its numerical value is exactly the ordinary
mathematical word setter on the original full label. The argument uses
symbolic bit readouts and never expands a concrete word or basis space.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

open EncodedBit.WindowLookup

attribute [local implicit_reducible] capacity width

private lemma port_cases (ports : PortAssignment) (port : WordPort) :
    port = ports.source ∨ port = ports.target ∨ port = ports.multiplier := by
  have first := ports.source_target
  have second := ports.source_multiplier
  have third := ports.target_multiplier
  cases source : ports.source <;> cases target : ports.target <;>
    cases multiplier : ports.multiplier <;> cases port <;> simp_all

/-- Numerical target replacement is an exact full-label equality, including all original padding. -/
lemma arithmeticState_target_set (ports : PortAssignment)
    (source target newTarget multiplier : Word)
    (retained : Placement.Rest ports) :
    arithmeticState ports source newTarget multiplier retained =
      resultSetConstant (⟨ports.target.bit⟩ : EncodedBit.Word Frame.encoding 256) newTarget
        (arithmeticState ports source target multiplier retained) := by
  apply EncodedBit.state_eq_of_get_eq Frame.encoding_surjective
  intro observed
  by_cases selected : ∃ port index, observed.wire = (WordPort.bit port index).wire
  · obtain ⟨port, index, same⟩ := selected
    rw [EncodedBit.eq_of_wire_eq observed (port.bit index) same]
    rcases port_cases ports port with rfl | rfl | rfl
    · rw [resultSetConstant_observed _ _ _
        (fun bit => WordPort.bit_ports_disjoint ports.target ports.source
          ports.source_target.symm bit index), WordPort.bit_get, WordPort.bit_get,
        arithmeticState_source, arithmeticState_source]
    · rw [resultSetConstant_get
        (⟨ports.target.bit⟩ : EncodedBit.Word Frame.encoding 256)
        (WordPort.bit_index_injective ports.target),
        WordPort.bit_get, arithmeticState_target]
    · rw [resultSetConstant_observed _ _ _
        (fun bit => WordPort.bit_ports_disjoint ports.target ports.multiplier
          ports.target_multiplier bit index), WordPort.bit_get, WordPort.bit_get,
        arithmeticState_multiplier, arithmeticState_multiplier]
  · have nonword : ∀ port index, observed.wire ≠ (WordPort.bit port index).wire := by
      intro port index same
      exact selected ⟨port, index, same⟩
    exact (arithmeticState_nonword ports observed nonword source target multiplier
      source newTarget multiplier retained).trans
      (resultSetConstant_observed _ _ observed
        (fun index => (nonword ports.target index).symm) _).symm

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
