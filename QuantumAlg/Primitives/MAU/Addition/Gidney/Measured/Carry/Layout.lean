/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Layout

/-!
# Actual source and dirty-output ports for carry xor

The carry-xor word reads a source prefix and xors its outgoing carries into
distinct arbitrary output bits. The same interface also permits a clean first
output and a separate comparison flag. Every source and control wire is
excluded from every carry output [G25, main.tex:253-271].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured

noncomputable section

/-- Physical ports of a carry prefix, without an initialization premise on its outputs. -/
structure CarryLayout {Data : Type} (encoding : BinaryLabelEncoding Data) (length : Nat) where
  control : EncodedBit encoding
  source : Fin length → EncodedBit encoding
  output : Fin length → EncodedBit encoding
  control_source_ne : ∀ index, control.wire ≠ (source index).wire
  control_output_ne : ∀ index, control.wire ≠ (output index).wire
  source_output_ne : ∀ first second, (source first).wire ≠ (output second).wire
  outputs_distinct : Function.Injective (fun index => (output index).wire)

namespace Layout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The measured adder borrows exactly its low `width - 2` target/carry-output pairs. -/
def carryLayout (layout : Layout encoding width) : CarryLayout encoding (width - 2) where
  control := layout.control
  source := fun index => layout.target ⟨index.val, by omega⟩
  output := layout.dirty
  control_source_ne := fun index => layout.control_target_ne ⟨index.val, by omega⟩
  control_output_ne := layout.control_dirty_ne
  source_output_ne := fun first second =>
    layout.target_dirty_ne ⟨first.val, by omega⟩ second
  outputs_distinct := fun first second equal => by
    have same := layout.distinct equal
    exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj same))

end Layout

namespace CarryLayout

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {length : Nat}

/-- Drop only the final source/output pair while retaining every physical address. -/
def lower {length : Nat} (layout : CarryLayout encoding (length + 1)) :
    CarryLayout encoding length where
  control := layout.control
  source := fun index => layout.source index.castSucc
  output := fun index => layout.output index.castSucc
  control_source_ne := fun index => layout.control_source_ne index.castSucc
  control_output_ne := fun index => layout.control_output_ne index.castSucc
  source_output_ne := fun first second => layout.source_output_ne first.castSucc second.castSucc
  outputs_distinct := fun first second equal => by
    apply Fin.ext
    exact congrArg (fun index : Fin (length + 1) => index.val) (layout.outputs_distinct equal)

/-- Distinct carry positions cannot address the same physical output bit. -/
lemma output_ne (layout : CarryLayout encoding length) {first second : Fin length}
    (different : first ≠ second) :
    (layout.output first).wire ≠ (layout.output second).wire :=
  fun equal => different (layout.outputs_distinct equal)

end CarryLayout

end

end QuantumAlg.MAU.Addition.Gidney.Measured
