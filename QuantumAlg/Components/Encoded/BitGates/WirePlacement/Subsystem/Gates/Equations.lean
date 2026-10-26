/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Gates

/-! # Native constructor equations without expanding a concrete completed wire frame -/

namespace QuantumAlg.EncodedBit.WireSubsystem

noncomputable section

variable {Source Target : Type} {source : BinaryLabelEncoding Source}
  {target : BinaryLabelEncoding Target} (placement : WireSubsystem source target)
  (sourceOnto : Function.Surjective source.encode)
  (targetOnto : Function.Surjective target.encode)

/-- Physical placement retains the distinctness of any two original native positions. -/
lemma placeBit_ne (first second : EncodedBit source) (different : first.wire ≠ second.wire) :
    (placement.placeBit sourceOnto targetOnto first).wire ≠
      (placement.placeBit sourceOnto targetOnto second).wire := by
  rw [placeBit_wire, placeBit_wire]
  exact fun same => different (placement.wires.injective same)

/-- A placed native X names precisely its original declared target position. -/
lemma placeGate_x (bit : EncodedBit source) :
    placement.placeGate sourceOnto targetOnto (.x bit) =
      .x (placement.placeBit sourceOnto targetOnto bit) := rfl

/-- A placed CNOT retains its complete ordered original operand positions. -/
lemma placeGate_cnot (control bit : EncodedBit source) (different : control.wire ≠ bit.wire) :
    placement.placeGate sourceOnto targetOnto (.cnot control bit different) =
      .cnot (placement.placeBit sourceOnto targetOnto control)
        (placement.placeBit sourceOnto targetOnto bit)
        (placement.placeBit_ne sourceOnto targetOnto control bit different) := rfl

/-- A placed Toffoli retains both ordered controls and the actual original target position. -/
lemma placeGate_toffoli (first second bit : EncodedBit source)
    (distinct : first.wire ≠ second.wire) (firstTarget : first.wire ≠ bit.wire)
    (secondTarget : second.wire ≠ bit.wire) :
    placement.placeGate sourceOnto targetOnto
        (.toffoli first second bit distinct firstTarget secondTarget) =
      .toffoli (placement.placeBit sourceOnto targetOnto first)
        (placement.placeBit sourceOnto targetOnto second)
        (placement.placeBit sourceOnto targetOnto bit)
        (placement.placeBit_ne sourceOnto targetOnto first second distinct)
        (placement.placeBit_ne sourceOnto targetOnto first bit firstTarget)
        (placement.placeBit_ne sourceOnto targetOnto second bit secondTarget) := rfl

end

end QuantumAlg.EncodedBit.WireSubsystem
