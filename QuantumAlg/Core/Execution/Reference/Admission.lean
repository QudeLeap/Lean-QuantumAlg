/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Support
import all QuantumAlg.Core.Execution.Borrowed.Support

/-!
# Independent local admission follows from complete reference observations

A zero bad-event observation at every reference coordinate excludes all
positive actual records outside the local domain. The proof groups real
blocks by one Boolean predicate; it neither enumerates runtime values nor
assumes that the algorithm has already satisfied its target contract.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

/-- Actual supported records in a domain give zero weight to its complement. -/
lemma referenceFiberSum_bad_eq_zero {C : Type} [Fintype C]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (domain : C → Prop) [DecidablePred domain]
    (admitted : ∀ record, 0 < (state.block record).mass → domain record)
    (left right : Reference.Index) :
    referenceFiberSum state (fun record _ => if domain record then 0 else 1) left right = 0 := by
  have same := referenceFiberSum_congr_on_positive state
    (fun record _ => if domain record then 0 else 1) (fun _ _ => 0)
    (by
      intro record positive basis
      simp only [admitted record positive, if_true]) left right
  refine same.trans ?_
  simp only [referenceFiberSum, zero_mul, Finset.sum_const_zero]

/-- Complete zero complement observations exclude every positive bad record. -/
lemma supported_of_reference_zero {C : Type} [Fintype C]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (domain : C → Prop) [DecidablePred domain]
    (zero : ∀ left right : Reference.Index,
      referenceFiberSum state (fun record _ => if domain record then 0 else 1) left right = 0)
    (record : C) (positive : 0 < (state.block record).mass) : domain record := by
  let read : C → Bool := fun record => decide (domain record)
  have weights : (fun record (_ : R.Index) => if read record = false then (1 : ℂ) else 0) =
      (fun record (_ : R.Index) => if domain record then (0 : ℂ) else 1) := by
    funext entry basis
    by_cases good : domain entry <;> simp only [read, good, decide_true, decide_false,
      Bool.true_eq_false, if_false, if_true]
  have empty : ((state.mapClassical read).block false).mass = 0 := by
    rw [mapClassical_block_mass_referenceFiberSum]
    simp only [weights, zero, Finset.sum_const_zero, Complex.zero_re]
  by_contra outside
  have badPositive : 0 < ((state.mapClassical read).block false).mass :=
    (mapClassical_block_mass_pos_iff state read false).mpr
      ⟨record, by simp only [read, outside, decide_false], positive⟩
  rw [empty] at badPositive
  exact (lt_irrefl 0) badPositive

end

end QuantumAlg.ExecutionState
