/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Finite classical branch partitions

Classical selection keeps exactly the existing blocks whose stored values
satisfy the selection. It neither normalizes a selected block nor changes
its quantum operator. Summing a finite family is permitted only when its
combined probability mass is at most one.

These are block-selection and matrix-sum laws for the probability-bearing
state representation [dW19, qcnotes.tex:5381,5409]. They introduce no quantum
operation or independent execution object. A typed instruction supplies its
actual storage read as the selector; the branch partition then reconstructs
the complete original state, including quantum correlations.
-/

namespace QuantumAlg
namespace ExecutionState

open scoped ComplexOrder

noncomputable section

variable {C D I : Type} [Fintype C] [Fintype I] {R : Register}

/-- Retain exactly the blocks satisfying a predicate on their actual classical
values, leaving every retained quantum operator unchanged. -/
def filterClassical (state : ExecutionState C R) (predicate : C → Prop)
    [DecidablePred predicate] : ExecutionState C R where
  block value := if predicate value then state.block value else DensityOperator.zero R
  total_le_one := by
    simp only [apply_ite DensityOperator.mass, DensityOperator.zero_mass]
    apply le_trans _ state.total_le_one
    apply Finset.sum_le_sum
    intro value _
    split
    · exact le_rfl
    · exact (state.block value).mass_nonneg

/-- Selection acts on complete quantum blocks, not on individual amplitudes. -/
@[simp] theorem filterClassical_block (state : ExecutionState C R)
    (predicate : C → Prop) [DecidablePred predicate] (value : C) :
    (state.filterClassical predicate).block value =
      if predicate value then state.block value else DensityOperator.zero R := rfl

/-- The mass of a selected state is the sum of exactly its selected blocks. -/
theorem filterClassical_mass (state : ExecutionState C R)
    (predicate : C → Prop) [DecidablePred predicate] :
    (state.filterClassical predicate).mass =
      ∑ value, if predicate value then (state.block value).mass else 0 := by
  simp only [mass, filterClassical_block, apply_ite DensityOperator.mass,
    DensityOperator.zero_mass]

/-- Classical selection cannot increase probability mass. -/
theorem filterClassical_mass_le (state : ExecutionState C R)
    (predicate : C → Prop) [DecidablePred predicate] :
    (state.filterClassical predicate).mass ≤ state.mass := by
  rw [filterClassical_mass]
  apply Finset.sum_le_sum
  intro value _
  split
  · exact le_rfl
  · exact (state.block value).mass_nonneg

/-- Keeping every classical block is the identity. -/
@[simp] theorem filterClassical_true (state : ExecutionState C R) :
    state.filterClassical (fun _ => True) = state := by
  apply ext
  intro value
  simp only [filterClassical_block, if_true]

/-- Keeping no classical block gives the zero state. -/
@[simp] theorem filterClassical_false (state : ExecutionState C R) :
    state.filterClassical (fun _ => False) = zero := by
  apply ext
  intro value
  simp only [filterClassical_block, if_false, zero_block]

/-- Select one result of a deterministic read of the existing classical value.
The read function is supplied by the typed interpreter's storage reference. -/
def selectClassical [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) (selected : D) : ExecutionState C R :=
  state.filterClassical (fun value => read value = selected)

/-- A branch retains a block exactly when its stored value selects that branch. -/
@[simp] theorem selectClassical_block [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) (selected : D) (value : C) :
    (state.selectClassical read selected).block value =
      if read value = selected then state.block value else DensityOperator.zero R := rfl

/-- A branch inconsistent with a classical read has the zero quantum block. -/
theorem selectClassical_block_eq_zero [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) (selected : D) (value : C) (different : read value ≠ selected) :
    (state.selectClassical read selected).block value = DensityOperator.zero R := by
  simp only [selectClassical_block, different, if_false]

/-- Every nonzero branch block is consistent with the actual classical read. -/
theorem selectClassical_read_eq_of_block_ne_zero [DecidableEq D]
    (state : ExecutionState C R) (read : C → D) (selected : D) (value : C)
    (nonzero : (state.selectClassical read selected).block value ≠ DensityOperator.zero R) :
    read value = selected := by
  by_contra different
  exact nonzero (state.selectClassical_block_eq_zero read selected value different)

/-- The selected branch's probability is read from its retained blocks. -/
theorem selectClassical_mass [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) (selected : D) :
    (state.selectClassical read selected).mass =
      ∑ value, if read value = selected then (state.block value).mass else 0 :=
  filterClassical_mass state (fun value => read value = selected)

/-- Distinct read results partition the original probability mass exactly. -/
theorem sum_selectClassical_mass [Fintype D] [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) :
    ∑ selected, (state.selectClassical read selected).mass = state.mass := by
  simp only [selectClassical_mass]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, mass]

/-- The complete family of selected branches has admissible total mass. -/
theorem sum_selectClassical_mass_le_one [Fintype D] [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) :
    ∑ selected, (state.selectClassical read selected).mass ≤ 1 := by
  rw [sum_selectClassical_mass]
  exact state.mass_le_one

/-- Sum finitely many probability-bearing states without normalizing them.
The explicit bound concerns their combined mass, not each summand separately. -/
def finiteSum (states : I → ExecutionState C R)
    (total : ∑ index, (states index).mass ≤ 1) : ExecutionState C R where
  block value :=
    { matrix := ∑ index, ((states index).block value).matrix
      positive := Matrix.posSemidef_sum _ (fun index _ =>
        ((states index).block value).positive)
      trace_le_one := by
        rw [Matrix.trace_sum, Complex.re_sum]
        apply le_trans _ total
        apply Finset.sum_le_sum
        intro index _
        exact (states index).block_mass_le value }
  total_le_one := by
    change (∑ value, (∑ index, ((states index).block value).matrix).trace.re) ≤ 1
    simp only [Matrix.trace_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    exact total

/-- Every matrix entry of a finite sum is the sum of the original blocks. -/
@[simp] theorem finiteSum_block_matrix (states : I → ExecutionState C R)
    (total : ∑ index, (states index).mass ≤ 1) (value : C) :
    ((finiteSum states total).block value).matrix =
      ∑ index, ((states index).block value).matrix := rfl

/-- A finite sum retains the exact combined probability of each classical block. -/
theorem finiteSum_block_mass (states : I → ExecutionState C R)
    (total : ∑ index, (states index).mass ≤ 1) (value : C) :
    ((finiteSum states total).block value).mass =
      ∑ index, ((states index).block value).mass := by
  simp only [DensityOperator.mass, finiteSum_block_matrix, Matrix.trace_sum,
    Complex.re_sum]

/-- Total probability mass is additive for an admissible finite sum. -/
theorem finiteSum_mass (states : I → ExecutionState C R)
    (total : ∑ index, (states index).mass ≤ 1) :
    (finiteSum states total).mass = ∑ index, (states index).mass := by
  simp only [mass, finiteSum_block_mass]
  rw [Finset.sum_comm]

/-- Splitting by the actual read value and summing all branches reconstructs
the complete original state, including every quantum off-diagonal entry. -/
theorem finiteSum_selectClassical [Fintype D] [DecidableEq D] (state : ExecutionState C R)
    (read : C → D) :
    finiteSum (state.selectClassical read)
        (state.sum_selectClassical_mass_le_one read) = state := by
  apply ext
  intro value
  apply DensityOperator.ext
  simp only [finiteSum_block_matrix, selectClassical_block,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end

end ExecutionState
end QuantumAlg
