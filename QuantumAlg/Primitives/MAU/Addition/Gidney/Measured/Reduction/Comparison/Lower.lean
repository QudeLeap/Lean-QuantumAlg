/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Comparison.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout

/-!
# Exact lower comparison workspace on the same original physical systems

The lower native word retains the full carry control and every original
source/output address except the high comparison flag. Its reverse restores
only those original lower outputs, without touching that flag or allocating
another helper [G25, main.tex:253-295].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

/-- The comparison prefix below its original flag, using exactly the same physical addresses. -/
def comparisonLowerLayout (layout : Layout encoding width) (wide : 2 ≤ width) :
    CarryLayout encoding (width - 1) where
  control := (layout.comparisonLayout wide).control
  source := fun index => (layout.comparisonLayout wide).source ⟨index.val, by omega⟩
  output := fun index => (layout.comparisonLayout wide).output ⟨index.val, by omega⟩
  control_source_ne := fun index => (layout.comparisonLayout wide).control_source_ne _
  control_output_ne := fun index => (layout.comparisonLayout wide).control_output_ne _
  source_output_ne := fun first second => (layout.comparisonLayout wide).source_output_ne _ _
  outputs_distinct := by
    intro first second same
    apply Fin.ext
    exact congrArg (fun index : Fin width => index.val)
      ((layout.comparisonLayout wide).outputs_distinct same)

/-- At a successor width this is precisely the original native carry interface's lower prefix. -/
lemma comparisonLowerLayout_eq_lower {length : Nat} (layout : Layout encoding (length + 1))
    (wide : 2 ≤ length + 1) :
    layout.comparisonLowerLayout wide = (layout.comparisonLayout wide).lower := rfl

/-- The lower uncomputation uses the same original clean low helper. -/
lemma comparisonLowerLayout_low_output (layout : Layout encoding width) (wide : 2 ≤ width) :
    (layout.comparisonLowerLayout wide).output ⟨0, by omega⟩ = layout.clean 0 := by
  change (layout.comparisonLayout wide).output ⟨0, by omega⟩ = layout.clean 0
  exact comparisonLayout_low_output layout wide

/-- The original flag is excluded from every lower carry output. -/
lemma comparisonLowerLayout_output_flag_ne (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 1)) :
    ((layout.comparisonLowerLayout wide).output index).wire ≠ layout.flag.wire := by
  have different : (⟨index.val, by omega⟩ : Fin width) ≠ ⟨width - 1, by omega⟩ := by
    intro equal
    have values := congrArg (fun value : Fin width => value.val) equal
    change index.val = width - 1 at values
    have inside := index.isLt
    omega
  have actual := (layout.comparisonLayout wide).output_ne different
  rw [comparisonLayout_high_output] at actual
  exact actual

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
