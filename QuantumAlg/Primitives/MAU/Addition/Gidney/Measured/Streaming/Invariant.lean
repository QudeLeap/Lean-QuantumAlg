/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Arithmetic
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Offset
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Streaming.Rows

/-!
# Original-data invariant for chronological streaming prefixes

Before the final row, the unique live helper contains the original incoming
carry; every earlier helper has undergone the actual physical reset. Dirty
outputs retain their arbitrary original values xored with the carries already
extracted. All source bits and carries refer to the same original target and
quantum-control label [G25, main.tex:209-251,271-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Readout invariant after a chronological prefix preceding the final high-target carry row. -/
structure PrefixInvariant (layout : Layout encoding width) (constant : BitVec width)
    (initial current : Data) (count : Nat) : Prop where
  control : layout.control.get current = layout.control.get initial
  target : ∀ index : Fin width,
    (layout.target index).get current =
      (((layout.target index).get initial ^^
        (constant.getLsbD index.val && layout.control.get initial)) ^^
          (if index.val < count then layout.carryInto constant initial index.val else false))
  dirty : ∀ index : Fin (width - 2),
    (layout.dirty index).get current =
      ((layout.dirty index).get initial ^^
        (if index.val + 1 < count then layout.carryInto constant initial (index.val + 1)
         else false))
  clean : ∀ helper : Fin 2,
    (layout.clean helper).get current =
      if helper.val = count % 2 then layout.carryInto constant initial count else false

/-- The actual initial CNOT offset establishes the invariant with both original helpers clean. -/
lemma offsetGates_prefixInvariant (layout : Layout encoding width) (constant : BitVec width)
    (initial : Data) (clean : ∀ helper, (layout.clean helper).get initial = false) :
    layout.PrefixInvariant constant initial (stepList (layout.offsetGates constant) initial) 0 := by
  constructor
  · exact offsetGates_other layout constant layout.control
      (fun index => (layout.control_target_ne index).symm) initial
  · intro index
    simp only [Nat.not_lt_zero, if_false, Bool.xor_false]
    exact offsetGates_target layout constant initial index
  · intro index
    simp only [Nat.not_lt_zero, if_false, Bool.xor_false]
    exact offsetGates_other layout constant (layout.dirty index)
      (fun target => layout.target_dirty_ne target index) initial
  · intro helper
    rw [offsetGates_other layout constant (layout.clean helper)
      (fun target => layout.target_clean_ne target helper), clean]
    change false = if helper.val = 0 then false else false
    simp only [ite_self]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Layout
