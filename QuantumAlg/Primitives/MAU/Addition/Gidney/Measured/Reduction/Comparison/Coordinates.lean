/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean.Coordinates

/-!
# Native CNOT and X coordinates of the original controlled comparison

The bounds include the full and reversed lower clean-low native words and
the actual flag CNOT. Only a native word is reversed; both original active
control Toffolis remain explicit [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Both native carry words and the flag CNOT are charged in the same actual comparator. -/
lemma comparisonGates_cnot_bound (layout : Layout encoding width) (wide : 2 ≤ width)
    (large : 3 ≤ width) (threshold : BitVec width) :
    ((layout.comparisonGates wide threshold).map cnotMultiplicity).sum ≤ 14 * width - 18 := by
  unfold comparisonGates
  split
  · simp
  · simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse]
    have full := CarryLayout.cleanLowGates_cnot_bound (layout.comparisonLayout wide) (-threshold)
    have lower := CarryLayout.cleanLowGates_cnot_bound (layout.comparisonLowerLayout wide)
      ((-threshold).setWidth (width - 1))
    rw [if_neg (by omega : ¬ width < 2)] at full
    rw [if_neg (by omega : ¬ width - 1 < 2)] at lower
    change 0 + _ + _ + 1 + 0 ≤ _
    omega

/-- The original controlled comparator contains no single-qubit native instruction. -/
lemma comparisonGates_x_count (layout : Layout encoding width) (wide : 2 ≤ width)
    (threshold : BitVec width) :
    ((layout.comparisonGates wide threshold).map xMultiplicity).sum = 0 := by
  unfold comparisonGates
  split
  · rfl
  · simp only [List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
      CarryLayout.cleanLowGates_x_count]
    rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
