/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.PMF
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Vector.Defs
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import all QuantumAlg.Util.PMF
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Point masses and finite weights of the existing repeated-sampling PMF

The existing independent vector distribution has the product of its point
probabilities. Its finite complex-weighted sum decomposes into a first sample
and the existing shorter vector distribution. These are pure probability
identities, including the empty-vector boundary; no execution or additional
sampling construction is introduced.
-/

namespace QuantumAlg.PMF

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {Sample : Type}

private def vectorConsEquiv (count : Nat) :
    (Sample × List.Vector Sample count) ≃ List.Vector Sample (count + 1) where
  toFun := fun pair => List.Vector.cons pair.1 pair.2
  invFun := fun vector => (vector.head, vector.tail)
  left_inv := fun pair => by
    obtain ⟨head, tail⟩ := pair
    simp only [List.Vector.head_cons, List.Vector.tail_cons]
  right_inv := List.Vector.cons_head_tail

private lemma map_cons_apply [Finite Sample] {count : Nat}
    (distribution : PMF (List.Vector Sample count))
    (selected first : Sample) (tail : List.Vector Sample count) :
    (distribution.map (List.Vector.cons selected)) (List.Vector.cons first tail) =
      if first = selected then distribution tail else 0 := by
  let : Fintype Sample := Fintype.ofFinite Sample
  rw [PMF.map_apply, tsum_fintype]
  simp only [List.Vector.eq_cons_iff, List.Vector.head_cons, List.Vector.tail_cons]
  by_cases same : first = selected
  · simp only [same, true_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [same, false_and, if_false, Finset.sum_const_zero]

/-- A nonempty vector's exact mass factors into its first sample and the existing tail PMF. -/
lemma independentReplicateVector_cons_apply [Finite Sample] (distribution : PMF Sample)
    (count : Nat) (first : Sample) (tail : List.Vector Sample count) :
    independentReplicateVector distribution (count + 1) (List.Vector.cons first tail) =
      distribution first * independentReplicateVector distribution count tail := by
  let : Fintype Sample := Fintype.ofFinite Sample
  rw [independentReplicateVector, PMF.bind_apply, tsum_fintype]
  simp only [map_cons_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Every point probability is the product of the original single-sample probabilities. -/
public lemma independentReplicateVector_apply_prod [Finite Sample] (distribution : PMF Sample) :
    ∀ (count : Nat) (samples : List.Vector Sample count),
      independentReplicateVector distribution count samples =
        ∏ index : Fin count, distribution (samples.get index) := by
  intro count
  induction count with
  | zero =>
      intro samples
      have empty : samples = List.Vector.nil := Subsingleton.elim _ _
      subst samples
      simp only [independentReplicateVector, PMF.pure_apply, if_true, Fin.prod_univ_zero]
  | succ count induction =>
      intro samples
      rw [← samples.cons_head_tail, independentReplicateVector_cons_apply,
        induction, Fin.prod_univ_succ]
      simp only [List.Vector.get_cons_zero, List.Vector.get_cons_succ]

/-- Finite real probabilities retain the same product, including zero-probability outcomes. -/
lemma independentReplicateVector_toReal_prod [Finite Sample] (distribution : PMF Sample)
    (count : Nat) (samples : List.Vector Sample count) :
    (independentReplicateVector distribution count samples).toReal =
      ∏ index : Fin count, (distribution (samples.get index)).toReal := by
  rw [independentReplicateVector_apply_prod, ENNReal.toReal_prod]

/-- Finite complex weights separate into the actual first-sample and tail-distribution sums. -/
lemma independentReplicateVector_weighted_cons [Fintype Sample] (distribution : PMF Sample)
    (count : Nat) (weight : List.Vector Sample (count + 1) → ℂ) :
    (∑ samples : List.Vector Sample (count + 1),
      ((independentReplicateVector distribution (count + 1) samples).toReal : ℂ) *
        weight samples) =
      ∑ first : Sample, ((distribution first).toReal : ℂ) *
        ∑ tail : List.Vector Sample count,
          ((independentReplicateVector distribution count tail).toReal : ℂ) *
            weight (List.Vector.cons first tail) := by
  have regrouped := (vectorConsEquiv (Sample := Sample) count).sum_comp
    (fun samples => ((independentReplicateVector distribution (count + 1) samples).toReal : ℂ) *
      weight samples)
  refine regrouped.symm.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  change ((independentReplicateVector distribution (count + 1)
    (List.Vector.cons first tail)).toReal : ℂ) * weight (List.Vector.cons first tail) = _
  rw [independentReplicateVector_cons_apply, ENNReal.toReal_mul, Complex.ofReal_mul, mul_assoc]

end

end QuantumAlg.PMF
