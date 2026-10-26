/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Layout

/-!
# Actual disjoint controls, target, dirty ports, helpers and reduction flag

Both active quantum controls, both clean helpers, the reduction flag and
every target wire are excluded from the arbitrary dirty word. The measured
adder uses that same flag as its coherent control and the same physical
target/dirty/helper ports. This interface introduces no allocated systems
[G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction

noncomputable section

/-- Two active controls, target, arbitrary dirty outputs, exactly two helpers and one flag. -/
abbrev Port (width : Nat) := Fin 2 ⊕ (Fin width ⊕ (Fin (width - 2) ⊕ (Fin 2 ⊕ Unit)))

/-- Actual original addresses with complete physical exclusion of all simultaneous live ports. -/
structure Layout {Data : Type} (encoding : BinaryLabelEncoding Data) (width : Nat) where
  bit : Port width → EncodedBit encoding
  distinct : Function.Injective (fun port => (bit port).wire)

namespace Layout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The retained global quantum control. -/
def control (layout : Layout encoding width) : EncodedBit encoding := layout.bit (.inl 0)

/-- The retained current source-word selection bit, excluded from the dirty ports. -/
def selector (layout : Layout encoding width) : EncodedBit encoding := layout.bit (.inl 1)

/-- The same original little-endian target word. -/
def target (layout : Layout encoding width) (index : Fin width) : EncodedBit encoding :=
  layout.bit (.inr (.inl index))

/-- Arbitrary dirty carry outputs excluding both active controls and all clean systems. -/
def dirty (layout : Layout encoding width) (index : Fin (width - 2)) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inl index)))

/-- Exactly the original two helper systems shared by comparisons and measured addition. -/
def clean (layout : Layout encoding width) (index : Fin 2) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inr (.inl index))))

/-- The one original clean reduction flag, used coherently by both measured offset additions. -/
def flag (layout : Layout encoding width) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inr (.inr ()))))

/-- Different simultaneous live port names have different actual physical identities. -/
lemma wire_ne (layout : Layout encoding width) {first second : Port width}
    (different : first ≠ second) :
    (layout.bit first).wire ≠ (layout.bit second).wire :=
  fun equal => different (layout.distinct equal)

private def adderPort : Measured.Port width → Port width
  | .inl singleton => .inr (.inr (.inr (.inr singleton)))
  | .inr (.inl index) => .inr (.inl index)
  | .inr (.inr (.inl index)) => .inr (.inr (.inl index))
  | .inr (.inr (.inr helper)) => .inr (.inr (.inr (.inl helper)))

private lemma adderPort_injective : Function.Injective (adderPort (width := width)) := by
  intro first second same
  rcases first with ⟨⟩ | firstTarget | firstDirty | firstHelper <;>
    rcases second with ⟨⟩ | secondTarget | secondDirty | secondHelper <;>
    simp_all [adderPort]

/-- The existing measured adder acts at these same physical ports with the original flag control. -/
def adderLayout (layout : Layout encoding width) : Measured.Layout encoding width where
  bit := fun port => layout.bit (adderPort port)
  distinct := layout.distinct.comp adderPort_injective

end Layout

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction
