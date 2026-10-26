/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.State.Vector.Gram

/-!
# Coherent collision norms with a constant source and arbitrary Reference

A constant source label contributes no additional branch distinction. Matching
physical and ideal label collisions therefore preserves the full coherent norm,
including every Reference cross term and zero-amplitude component.
-/

namespace QuantumAlg.HilbertVector

noncomputable section

open scoped BigOperators

/-- Constant source labels and equal branch collisions preserve coherent Reference norms. -/
lemma norm_sum_sum_smul_ket_eq_of_eq_iff {Branch : Type} [Fintype Branch]
    {Physical Source Group Reference : Register}
    (physical : Branch → Physical.Index) (remaining : Branch → Source.Index)
    (zero : Source.Index) (group : Branch → Group.Index)
    (remainingZero : ∀ branch, remaining branch = zero)
    (same : ∀ first last, physical first = physical last ↔ group first = group last)
    (amplitude : Branch → ℂ) (reference : HilbertVector Reference) :
    ‖∑ branch, ∑ ref : Reference.Index,
      (amplitude branch * reference ref) •
        (NormalizedVector.ket (R := Physical.prod (Source.prod Reference))
          (physical branch, remaining branch, ref)).vec‖ =
      ‖∑ branch, ∑ ref : Reference.Index,
        (amplitude branch * reference ref) •
          (NormalizedVector.ket (R := Group.prod Reference) (group branch, ref)).vec‖ := by
  let first : Branch × Reference.Index → (Physical.prod (Source.prod Reference)).Index :=
    fun index => (physical index.1, remaining index.1, index.2)
  let last : Branch × Reference.Index → (Group.prod Reference).Index :=
    fun index => (group index.1, index.2)
  let coefficient : Branch × Reference.Index → ℂ :=
    fun index => amplitude index.1 * reference index.2
  let firstVector : Branch × Reference.Index →
      HilbertVector (Physical.prod (Source.prod Reference)) :=
    fun index => coefficient index •
      (NormalizedVector.ket (R := Physical.prod (Source.prod Reference)) (first index)).vec
  let lastVector : Branch × Reference.Index → HilbertVector (Group.prod Reference) :=
    fun index => coefficient index •
      (NormalizedVector.ket (R := Group.prod Reference) (last index)).vec
  have firstSum : (∑ index : Branch × Reference.Index, firstVector index) =
      ∑ branch : Branch, ∑ ref : Reference.Index, firstVector (branch, ref) :=
    Fintype.sum_prod_type firstVector
  have lastSum : (∑ index : Branch × Reference.Index, lastVector index) =
      ∑ branch : Branch, ∑ ref : Reference.Index, lastVector (branch, ref) :=
    Fintype.sum_prod_type lastVector
  have gram : ‖∑ index : Branch × Reference.Index, firstVector index‖ =
      ‖∑ index : Branch × Reference.Index, lastVector index‖ := by
    refine HilbertVector.norm_sum_smul_ket_eq_of_eq_iff
      (R := Physical.prod (Source.prod Reference)) (S := Group.prod Reference)
      (Branch := Branch × Reference.Index) Finset.univ first last ?_ coefficient
    intro left _ right _
    change (physical left.1, remaining left.1, left.2) =
      (physical right.1, remaining right.1, right.2) ↔
      (group left.1, left.2) = (group right.1, right.2)
    simp only [Prod.mk.injEq, remainingZero, true_and, same]
  exact (congrArg
    (fun vector : HilbertVector (Physical.prod (Source.prod Reference)) => ‖vector‖)
    firstSum).symm.trans (gram.trans (congrArg
      (fun vector : HilbertVector (Group.prod Reference) => ‖vector‖) lastSum))

end

end QuantumAlg.HilbertVector
