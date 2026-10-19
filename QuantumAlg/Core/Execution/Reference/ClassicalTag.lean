/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Base.State.Density.ReferenceBlock
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Classical labels as diagonal external-reference blocks

These mathematical maps move a finite classical label into an external
reference register and recover it by taking its diagonal blocks. They retain
the original quantum matrix, including every off-diagonal reference entry,
and do not condition or normalize a branch. They add no circuit instruction,
physical storage allocation, or operational conversion.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {C : Type} [Fintype C] {Tag R : Register}

/-- Place each classical label in its own external basis block before forgetting the label. -/
private def classicalTagBlocks (state : ExecutionState (C × Tag.Index) R) :
    ExecutionState (C × Tag.Index) (Tag.prod R) where
  block record := Execution.prependPrepared (state.block record)
    (NormalizedVector.ket record.2)
  total_le_one := by
    simp only [Execution.prependPrepared_mass]
    exact state.total_le_one

private lemma classicalTagBlocks_mass (state : ExecutionState (C × Tag.Index) R) :
    (classicalTagBlocks state).mass = state.mass := by
  simp only [mass, classicalTagBlocks, Execution.prependPrepared_mass]

private lemma classicalTagBlocks_entry (state : ExecutionState (C × Tag.Index) R)
    (record : C × Tag.Index) (leftTag rightTag : Tag.Index) (left right : R.Index) :
    ((classicalTagBlocks state).block record).matrix (leftTag, left) (rightTag, right) =
      if leftTag = record.2 ∧ rightTag = record.2 then
        (state.block record).matrix left right else 0 := by
  change ((NormalizedVector.ket record.2) leftTag *
    star ((NormalizedVector.ket record.2) rightTag)) *
      (state.block record).matrix left right = _
  rw [NormalizedVector.ket_apply, NormalizedVector.ket_apply]
  by_cases first : leftTag = record.2 <;> by_cases second : rightTag = record.2 <;>
    simp only [first, second, and_self, and_false, false_and, if_true, if_false,
      star_one, star_zero, one_mul, zero_mul, mul_zero]

/-- Encode a finite classical label as an orthogonal external-reference basis block. -/
def encodeClassicalTag (state : ExecutionState (C × Tag.Index) R) :
    ExecutionState C (Tag.prod R) :=
  (classicalTagBlocks state).mapClassical Prod.fst

/-- Encoding retains the total mass, including for subnormalized input. -/
lemma encodeClassicalTag_mass (state : ExecutionState (C × Tag.Index) R) :
    (encodeClassicalTag state).mass = state.mass :=
  (mapClassical_mass _ _).trans (classicalTagBlocks_mass state)

/-- Every diagonal tag block is the complete original matrix; distinct tags have no coherence. -/
lemma encodeClassicalTag_entry (state : ExecutionState (C × Tag.Index) R)
    (label : C) (leftTag rightTag : Tag.Index) (left right : R.Index) :
    ((encodeClassicalTag state).block label).matrix (leftTag, left) (rightTag, right) =
      if leftTag = rightTag then (state.block (label, leftTag)).matrix left right else 0 := by
  simp only [encodeClassicalTag, mapClassical_block_matrix,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    classicalTagBlocks_entry, Fintype.sum_prod_type]
  by_cases same : leftTag = rightTag
  · subst rightTag
    simp
  · have distinct (tag : Tag.Index) : ¬ (leftTag = tag ∧ rightTag = tag) := by
      rintro ⟨first, second⟩
      exact same (first.trans second.symm)
    simp [distinct, same]

private lemma sum_classicalTagSlices_mass (state : ExecutionState C (Tag.prod R)) :
    (∑ record : C × Tag.Index, ((state.block record.1).basisSlice record.2).mass) =
      state.mass := by
  rw [Fintype.sum_prod_type]
  unfold mass
  apply Finset.sum_congr rfl
  intro label _
  change (∑ tag : Tag.Index,
      (∑ index : R.Index, (state.block label).matrix (tag, index) (tag, index)).re) =
    (∑ index : Tag.Index × R.Index, (state.block label).matrix index index).re
  rw [Fintype.sum_prod_type, Complex.re_sum]

/-- Observe the tag basis without normalizing any branch, retaining the complete old register. -/
def decodeClassicalTag (state : ExecutionState C (Tag.prod R)) :
    ExecutionState (C × Tag.Index) R where
  block record := (state.block record.1).basisSlice record.2
  total_le_one := (sum_classicalTagSlices_mass state).trans_le state.mass_le_one

/-- The diagonal tag blocks contain the entire trace of any input state. -/
lemma decodeClassicalTag_mass (state : ExecutionState C (Tag.prod R)) :
    (decodeClassicalTag state).mass = state.mass :=
  sum_classicalTagSlices_mass state

/-- Decoding retains every original-register matrix entry at the chosen tag. -/
lemma decodeClassicalTag_entry (state : ExecutionState C (Tag.prod R))
    (label : C) (tag : Tag.Index) (left right : R.Index) :
    ((decodeClassicalTag state).block (label, tag)).matrix left right =
      (state.block label).matrix (tag, left) (tag, right) := rfl

/-- Every original classical-quantum correlation is recovered exactly after encoding. -/
lemma decode_encodeClassicalTag (state : ExecutionState (C × Tag.Index) R) :
    decodeClassicalTag (encodeClassicalTag state) = state := by
  apply ExecutionState.ext
  intro record
  apply DensityOperator.ext
  ext left right
  rw [decodeClassicalTag_entry, encodeClassicalTag_entry]
  simp

/-- Forgetting the decoded label takes the exact partial trace over its external register. -/
lemma decodeClassicalTag_forget_entry (state : ExecutionState C (Tag.prod R))
    (label : C) (left right : R.Index) :
    (((decodeClassicalTag state).mapClassical Prod.fst).block label).matrix left right =
      ∑ tag : Tag.Index, (state.block label).matrix (tag, left) (tag, right) := by
  simp only [mapClassical_block_matrix, decodeClassicalTag,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply,
    DensityOperator.basisSlice_matrix, Fintype.sum_prod_type]
  simp

/-- The original label-forgotten state is unchanged by the tag representation. -/
lemma decode_encodeClassicalTag_forget (state : ExecutionState (C × Tag.Index) R) :
    (decodeClassicalTag (encodeClassicalTag state)).mapClassical Prod.fst =
      state.mapClassical Prod.fst := by
  rw [decode_encodeClassicalTag]

end

end QuantumAlg.ExecutionState
