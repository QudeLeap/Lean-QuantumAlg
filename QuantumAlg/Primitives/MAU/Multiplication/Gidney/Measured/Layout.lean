/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Layout

/-!
# Actual constant-workspace measured modular-multiplication ports

The original global control, two complete words, two clean adder helpers
and one reduction flag form exactly `2n+4` simultaneous physical systems.
Each selected modular addition borrows dirty outputs only from other bits
of its retained source word [G25, main.tex:271-295,354-360].
-/

namespace QuantumAlg.MAU.Multiplication.Gidney.Measured

noncomputable section

/-- Global control, source word, target word, exactly two adder helpers and one flag. -/
abbrev Port (width : Nat) := Unit ⊕ (Fin width ⊕ (Fin width ⊕ (Fin 2 ⊕ Unit)))

/-- Original simultaneous physical addresses, without any dirty-state initialization promise. -/
structure Layout {Data : Type} (encoding : BinaryLabelEncoding Data) (width : Nat) where
  bit : Port width → EncodedBit encoding
  distinct : Function.Injective (fun port => (bit port).wire)

namespace Layout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The single retained global coherent multiplication control. -/
def control (layout : Layout encoding width) : EncodedBit encoding := layout.bit (.inl ())

/-- The retained source word whose selected bit controls each actual modular-addition row. -/
def source (layout : Layout encoding width) (index : Fin width) : EncodedBit encoding :=
  layout.bit (.inr (.inl index))

/-- The actual target accumulator word. -/
def target (layout : Layout encoding width) (index : Fin width) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inl index)))

/-- The same original two clean helper systems shared by every measured addition. -/
def clean (layout : Layout encoding width) (index : Fin 2) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inr (.inl index))))

/-- The same original clean flag physically restored by every modular-addition row. -/
def flag (layout : Layout encoding width) : EncodedBit encoding :=
  layout.bit (.inr (.inr (.inr (.inr ()))))

/-- Different simultaneous port names have different original physical identities. -/
lemma wire_ne (layout : Layout encoding width) {first second : Port width}
    (different : first ≠ second) :
    (layout.bit first).wire ≠ (layout.bit second).wire :=
  fun equal => different (layout.distinct equal)

/-- The simultaneous original frame has exactly the promised constant-workspace width. -/
lemma multiplication_port_card (width : Nat) : Fintype.card (Port width) = 2 * width + 4 := by
  simp only [Port, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

end Layout

end

end QuantumAlg.MAU.Multiplication.Gidney.Measured
