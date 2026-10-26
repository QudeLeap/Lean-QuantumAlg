/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Gates
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Clean.Uncompute

/-!
# Full comparison carry computation followed by its actual lower uncomputation

The two literal native words restore every original lower carry output.
Their only remaining action is a full-width carry xor into the same original
flag. The original dirty word and flag are arbitrary, and the low helper is
the only initialized carry output [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

open EncodedBit GateSpec

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- Exact complete-label action of the actual comparison's native carry pair. -/
lemma comparisonCarry_step (layout : Layout encoding width) (wide : 2 ≤ width)
    (constant : BitVec width) (state : Data) (clean : (layout.clean 0).get state = false) :
    stepList ((layout.comparisonLowerLayout wide).cleanLowGates
        (constant.setWidth (width - 1))).reverse
      (stepList ((layout.comparisonLayout wide).cleanLowGates constant) state) =
        if (layout.comparisonLayout wide).carryValues constant state width then
          layout.flag.flip state else state := by
  obtain ⟨length, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width ≠ 0)
  rw [comparisonLowerLayout_eq_lower]
  have initial : ((layout.comparisonLayout wide).output ⟨0, by omega⟩).get state = false := by
    rw [comparisonLayout_low_output]
    exact clean
  have actual := CarryLayout.cleanLowGates_uncompute_top (layout.comparisonLayout wide)
    constant (by omega) state initial
  have high : (layout.comparisonLayout wide).output (Fin.last length) = layout.flag := by
    exact comparisonLayout_high_output layout wide
  rw [high] at actual
  exact actual

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
