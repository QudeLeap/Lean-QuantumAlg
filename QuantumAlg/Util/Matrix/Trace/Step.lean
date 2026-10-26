/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One-step decomposition of finite matrix-valued traces

Finite branch paths and retained Store observations compose by exact ordered
matrix sandwiches. The algebra is proved on abstract finite carriers before
instantiating any circuit, point program, runtime context or external Reference.
-/

namespace QuantumAlg.MatrixTrace

noncomputable section

open scoped BigOperators

local instance {Index : Type} : DecidableEq Index := Classical.decEq Index
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma sum_at_condition {I J : Type} [Fintype I] [DecidableEq I]
    (selected : I) (condition : I → Prop) (value : Matrix J J ℂ) :
    (∑ index : I, if condition index then if selected = index then value else 0 else 0) =
      if condition selected then value else 0 := by
  have each (index : I) :
      (if condition index then if selected = index then value else 0 else 0) =
        if selected = index then if condition selected then value else 0 else 0 := by
    by_cases same : selected = index
    · subst index
      simp only [if_true]
    · simp only [if_neg same, ite_self]
  simp only [each, Fintype.sum_ite_eq]

private lemma sandwich_sum {I J : Type} [Fintype I] [Fintype J]
    (operator : Matrix J J ℂ) (predicate : I → Prop) (value : I → Matrix J J ℂ) :
    operator * (∑ index : I, if predicate index then value index else 0) *
        operator.conjTranspose =
      ∑ index : I, if predicate index then
        operator * value index * operator.conjTranspose else 0 := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  by_cases selected : predicate index
  · rw [if_pos selected, if_pos selected]
  · rw [if_neg selected, if_neg selected, Matrix.mul_zero, Matrix.zero_mul]

private lemma collapse_written_sum {I Branch J : Type}
    [Fintype I] [Fintype Branch] [Fintype J]
    (operator : Matrix J J ℂ) (follows : I → Prop) (written : Branch → I)
    (value : Branch → Matrix J J ℂ) (step : I → Matrix J J ℂ)
    (entry : ∀ original, step original =
      ∑ branch : Branch, if written branch = original then value branch else 0) :
    (∑ original : I, if follows original then
      operator * step original * operator.conjTranspose else 0) =
    ∑ branch : Branch, if follows (written branch) then
      operator * value branch * operator.conjTranspose else 0 := by
  calc
    _ = ∑ original : I, ∑ branch : Branch, if follows original then
        if written branch = original then
          operator * value branch * operator.conjTranspose else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro original _
      rw [entry]
      by_cases selected : follows original
      · simp only [if_pos selected]
        exact sandwich_sum operator (fun branch => written branch = original) value
      · simp only [if_neg selected, Finset.sum_const_zero]
    _ = ∑ branch : Branch, ∑ original : I, if follows original then
        if written branch = original then
          operator * value branch * operator.conjTranspose else 0 else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro branch _
      exact sum_at_condition (written branch) follows
        (operator * value branch * operator.conjTranspose)

private lemma retained_sandwich {I J : Type} [Fintype I] [Fintype J]
    (left right : Matrix J J ℂ) (keep : I → Prop) (selected : Prop)
    (density : I → Matrix J J ℂ) :
    (∑ original : I, if keep original ∧ selected then
      (left * right) * density original * (left * right).conjTranspose else 0) =
    if selected then
      left * (right * (∑ original : I, if keep original then density original else 0) *
        right.conjTranspose) * left.conjTranspose else 0 := by
  by_cases active : selected
  · simp only [active, and_true, if_true]
    have grouped :
        left * (right * (∑ original : I, if keep original then density original else 0) *
          right.conjTranspose) * left.conjTranspose =
        (left * right) * (∑ original : I, if keep original then density original else 0) *
          (left * right).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [grouped]
    exact (sandwich_sum (left * right) keep density).symm
  · simp only [active, and_false, if_false, Finset.sum_const_zero]

/-- Split one finite trace step before instantiating its Store and quantum carriers. -/
lemma sum_cons {StoreIndex BranchIndex QuantumIndex : Type}
    [Fintype StoreIndex] [Fintype BranchIndex] [Fintype QuantumIndex]
    (count : Nat) (head : BranchIndex → Matrix QuantumIndex QuantumIndex ℂ)
    (written : BranchIndex → StoreIndex) (keeps : BranchIndex → StoreIndex → Prop)
    (tail : (Fin count → BranchIndex) → Matrix QuantumIndex QuantumIndex ℂ)
    (follows : (Fin count → BranchIndex) → StoreIndex → Prop)
    (density step : StoreIndex → Matrix QuantumIndex QuantumIndex ℂ)
    (entry : ∀ stored, step stored = ∑ branch : BranchIndex,
      if written branch = stored then
        head branch * (∑ original : StoreIndex,
          if keeps branch original then density original else 0) *
            (head branch).conjTranspose else 0) :
    (∑ path : Fin (count + 1) → BranchIndex, ∑ original : StoreIndex,
      if keeps (path 0) original ∧ follows (Fin.tail path) (written (path 0)) then
        (tail (Fin.tail path) * head (path 0)) * density original *
          (tail (Fin.tail path) * head (path 0)).conjTranspose else 0) =
      ∑ path : Fin count → BranchIndex, ∑ stored : StoreIndex,
        if follows path stored then tail path * step stored * (tail path).conjTranspose
        else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (count + 1) => BranchIndex)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.consEquiv_apply, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro path _
  let value := fun branch : BranchIndex =>
    head branch * (∑ original : StoreIndex,
      if keeps branch original then density original else 0) * (head branch).conjTranspose
  have collapsed := collapse_written_sum (tail path) (follows path) written value step entry
  refine Eq.trans (b := ∑ branch : BranchIndex,
    if follows path (written branch) then
      tail path * value branch * (tail path).conjTranspose else 0) ?_ collapsed.symm
  apply Finset.sum_congr rfl
  intro branch _
  exact retained_sandwich (tail path) (head branch) (keeps branch)
    (follows path (written branch)) density

end

end QuantumAlg.MatrixTrace
