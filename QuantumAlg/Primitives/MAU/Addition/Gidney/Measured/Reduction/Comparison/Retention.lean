/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Semantics

/-!
# Original physical readouts after the complete native comparison

The full-label flag-only law retains all other original systems and makes
the flag xor explicit. Dirty outputs and both helpers have no unrecorded
residual action [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Every original physical bit other than the flag is unchanged by the complete native word. -/
lemma comparisonGates_get (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (observed : EncodedBit encoding)
    (outside : layout.flag.wire ≠ observed.wire) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) :
    observed.get (stepList (layout.comparisonGates wide threshold) state) = observed.get state := by
  rw [comparisonGates_step layout wide threshold state clean]
  split_ifs
  · exact get_flip_of_wire_ne layout.flag observed outside state
  · rfl

/-- The original target word is retained by both native comparison passes. -/
lemma comparisonGates_sourceWord (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) :
    layout.sourceWord (stepList (layout.comparisonGates wide threshold) state) =
      layout.sourceWord state := by
  unfold sourceWord
  congr 1
  funext index
  exact comparisonGates_get layout wide threshold (layout.target index)
    (layout.wire_ne (by intro impossible; cases impossible)) state clean

/-- The actual flag contains precisely its arbitrary original bit xored with strict comparison. -/
lemma comparisonGates_flag (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) (state : Data)
    (clean : ∀ helper, (layout.clean helper).get state = false) :
    layout.flag.get (stepList (layout.comparisonGates wide threshold) state) =
      (layout.flag.get state ^^ ((layout.control.get state && layout.selector.get state) &&
        decide ((layout.sourceWord state).toNat < threshold.toNat))) := by
  rw [comparisonGates_step layout wide threshold state clean]
  cases (layout.control.get state && layout.selector.get state) &&
    decide ((layout.sourceWord state).toNat < threshold.toNat) <;>
      simp [get_flip_self]

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
