/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Reduction.Layout
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Carry.Layout

/-!
# Comparison carry ports on the original two helpers, dirty word and reduction flag

The original helper one temporarily holds the conjunction of the two active
controls. The native carry prefix has exactly the original target width:
helper zero is its low output, the original dirty word supplies its middle
outputs, and the existing reduction flag is its high output. All exclusions
follow from physical port injectivity [G25, main.tex:253-295,354-360].
-/

namespace QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private def comparisonOutputPort (wide : 2 ≤ width) (index : Fin width) : Port width :=
  if first : index.val = 0 then .inr (.inr (.inr (.inl 0)))
  else if final : index.val = width - 1 then .inr (.inr (.inr (.inr ())))
  else .inr (.inr (.inl ⟨index.val - 1, by
    have inside := index.isLt
    omega⟩))

private lemma comparisonOutputPort_injective (wide : 2 ≤ width) :
    Function.Injective (comparisonOutputPort wide) := by
  intro first second same
  unfold comparisonOutputPort at same
  split_ifs at same <;>
    simp only [Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl] at same
  all_goals
    apply Fin.ext
    first
    | omega
    | have values := congrArg (fun index : Fin (width - 2) => index.val) same
      change first.val - 1 = second.val - 1 at values
      have firstInside := first.isLt
      have secondInside := second.isLt
      omega

/-- The full native comparison carry uses only the existing helpers, dirty outputs and flag. -/
def comparisonLayout (layout : Layout encoding width) (wide : 2 ≤ width) :
    CarryLayout encoding width where
  control := layout.clean 1
  source := layout.target
  output := fun index => layout.bit (comparisonOutputPort wide index)
  control_source_ne := fun index => layout.wire_ne (by intro impossible; cases impossible)
  control_output_ne := fun index => layout.wire_ne (by
    unfold comparisonOutputPort
    split_ifs <;> simp)
  source_output_ne := fun first second => layout.wire_ne (by
    unfold comparisonOutputPort
    split_ifs <;> simp)
  outputs_distinct := layout.distinct.comp (comparisonOutputPort_injective wide)

/-- The original first helper is exactly the low comparison carry output. -/
lemma comparisonLayout_low_output (layout : Layout encoding width) (wide : 2 ≤ width) :
    (layout.comparisonLayout wide).output ⟨0, by omega⟩ = layout.clean 0 := by
  simp only [comparisonLayout, comparisonOutputPort, dite_true, clean]

/-- The same original reduction flag is exactly the high comparison carry output. -/
lemma comparisonLayout_high_output (layout : Layout encoding width) (wide : 2 ≤ width) :
    (layout.comparisonLayout wide).output ⟨width - 1, by omega⟩ = layout.flag := by
  simp only [comparisonLayout, comparisonOutputPort, dif_neg (by omega : width - 1 ≠ 0),
    dite_true, flag]

/-- Every middle comparison carry output is precisely its supplied arbitrary dirty port. -/
lemma comparisonLayout_middle_output (layout : Layout encoding width) (wide : 2 ≤ width)
    (index : Fin (width - 2)) :
    (layout.comparisonLayout wide).output ⟨index.val + 1, by omega⟩ = layout.dirty index := by
  simp only [comparisonLayout, comparisonOutputPort,
    dif_neg (by have inside := index.isLt; omega : index.val + 1 ≠ 0),
    dif_neg (by have inside := index.isLt; omega : index.val + 1 ≠ width - 1)]
  rfl

end

end QuantumAlg.MAU.Addition.Gidney.Measured.Reduction.Layout
