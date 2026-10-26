/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.GateSpec

/-!
# Explicit disjoint ports for the measured constant adder

The interface names one quantum control, the target word, exactly two clean
carry bits and the available dirty carry outputs. Injectivity of the physical
port map excludes the control and both clean bits from the dirty word. No
initialization condition is imposed on the dirty ports or any other encoded
wire [G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

/-- Semantic names of the actual physical ports; word positions are little endian. -/
abbrev Port (width : Nat) := Unit ⊕ (Fin width ⊕ (Fin (width - 2) ⊕ Fin 2))

/-- The actual addressed bits and a proof that none of their physical wires overlap. -/
structure Layout {Data : Type} (encoding : BinaryLabelEncoding Data) (width : Nat) where
  bit : Port width → EncodedBit encoding
  distinct : Function.Injective (fun port => (bit port).wire)

namespace Layout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The quantum addition control is retained throughout every measurement record. -/
def control (layout : Layout encoding width) : EncodedBit encoding :=
  layout.bit (.inl ())

/-- A target bit, indexed from the least significant bit. -/
def target (layout : Layout encoding width) (index : Fin width) : EncodedBit encoding :=
  layout.bit (.inr (.inl index))

/-- An arbitrary dirty carry output, disjoint from every control and target bit. -/
def dirty (layout : Layout encoding width) (index : Fin (width - 2)) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inl index)))

/-- One of the two clean carry bits, physically reset after every vent. -/
def clean (layout : Layout encoding width) (index : Fin 2) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inr index)))

/-- Distinct port names give distinct actual addressed physical wires. -/
lemma wire_ne (layout : Layout encoding width) {first second : Port width}
    (different : first ≠ second) :
    (layout.bit first).wire ≠ (layout.bit second).wire :=
  fun equal => different (layout.distinct equal)

lemma control_target_ne (layout : Layout encoding width) (index : Fin width) :
    layout.control.wire ≠ (layout.target index).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma control_dirty_ne (layout : Layout encoding width) (index : Fin (width - 2)) :
    layout.control.wire ≠ (layout.dirty index).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma control_clean_ne (layout : Layout encoding width) (index : Fin 2) :
    layout.control.wire ≠ (layout.clean index).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma target_dirty_ne (layout : Layout encoding width)
    (first : Fin width) (second : Fin (width - 2)) :
    (layout.target first).wire ≠ (layout.dirty second).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma target_clean_ne (layout : Layout encoding width) (first : Fin width) (second : Fin 2) :
    (layout.target first).wire ≠ (layout.clean second).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma dirty_clean_ne (layout : Layout encoding width)
    (first : Fin (width - 2)) (second : Fin 2) :
    (layout.dirty first).wire ≠ (layout.clean second).wire :=
  layout.wire_ne (by intro impossible; cases impossible)

lemma target_target_ne (layout : Layout encoding width) {first second : Fin width}
    (different : first ≠ second) :
    (layout.target first).wire ≠ (layout.target second).wire :=
  layout.wire_ne (fun equal => different (Sum.inl.inj (Sum.inr.inj equal)))

lemma dirty_dirty_ne (layout : Layout encoding width) {first second : Fin (width - 2)}
    (different : first ≠ second) :
    (layout.dirty first).wire ≠ (layout.dirty second).wire :=
  layout.wire_ne (fun equal => different (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj equal))))

lemma clean_clean_ne (layout : Layout encoding width) {first second : Fin 2}
    (different : first ≠ second) :
    (layout.clean first).wire ≠ (layout.clean second).wire :=
  layout.wire_ne (fun equal => different (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj equal))))

end Layout

end

end QuantumAlg.MAU.Addition.Gidney.Measured
