/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Weight
import all QuantumAlg.Core.Execution.Circuit.Support

/-!
# Quadratic observations of complete retained matrix sums

Full record fibers determine the observed effect on every normalized input.
Homogeneity extends that equality to arbitrary raw vectors, preserving zero
vectors and their original mass without renormalizing intermediate branches.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

private lemma raw_outer_quadratic {R : Register} (matrix : HilbertOperator R)
    (vector : HilbertVector R) :
    (matrix * Matrix.vecMulVec (fun index => vector index)
      (fun index => star (vector index))).trace.re =
      HilbertOperator.quadraticWeight matrix vector := by
  unfold HilbertOperator.quadraticWeight
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    HilbertOperator.applyVec_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro other _
  ring

private lemma weighted_sandwich_pure {R : Register}
    (effect operator : HilbertOperator R) (vector : NormalizedVector R) :
    (effect * (operator * (DensityOperator.ofPure vector).matrix *
      operator.conjTranspose)).trace.re =
      HilbertOperator.quadraticWeight effect (operator.applyVec vector) := by
  let values : R.Index → Complex := fun index => vector index
  change (effect * (operator * Matrix.vecMulVec values (star values) *
    operator.conjTranspose)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec operator values]
  exact raw_outer_quadratic effect (operator.applyVec vector)

private lemma quadratic_real_smul {R : Register} (matrix : HilbertOperator R)
    (scalar : Real) (vector : HilbertVector R) :
    HilbertOperator.quadraticWeight matrix ((scalar : Complex) • vector) =
      scalar ^ 2 * HilbertOperator.quadraticWeight matrix vector := by
  unfold HilbertOperator.quadraticWeight
  rw [HilbertOperator.applyVec_smul, inner_smul_right, inner_smul_left]
  simp only [starRingEnd_apply]
  have conjugate : star (scalar : Complex) = (scalar : Complex) :=
    Complex.conj_ofReal scalar
  rw [conjugate, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring


private lemma homogeneous_of_normalized {R : Register}
    (first second : HilbertVector R → Real)
    (firstScale : ∀ (scalar : Real) vector,
      first ((scalar : Complex) • vector) = scalar ^ 2 * first vector)
    (secondScale : ∀ (scalar : Real) vector,
      second ((scalar : Complex) • vector) = scalar ^ 2 * second vector)
    (zero : first 0 = second 0)
    (agrees : ∀ vector : NormalizedVector R, first vector.vec = second vector.vec)
    (vector : HilbertVector R) : first vector = second vector := by
  by_cases absent : vector = 0
  · subst vector
    exact zero
  · let unit : NormalizedVector R := NormalizedVector.ofNeZero vector absent
    have reconstruct : (‖vector‖ : Complex) • unit.vec = vector :=
      NormalizedVector.norm_smul_coe_ofNeZero vector absent
    exact (congrArg first reconstruct.symm).trans
      ((firstScale ‖vector‖ unit.vec).trans
        ((congrArg (fun value : Real => ‖vector‖ ^ 2 * value) (agrees unit)).trans
          ((secondScale ‖vector‖ unit.vec).symm.trans (congrArg second reconstruct))))

private lemma quadratic_sum_of_normalized {R : Register} {Outcome : Type} [Fintype Outcome]
    (matrix : HilbertOperator R) (effects operators : Outcome → HilbertOperator R)
    (agrees : ∀ vector : NormalizedVector R,
      HilbertOperator.quadraticWeight matrix vector =
        ∑ outcome, HilbertOperator.quadraticWeight (effects outcome)
          ((operators outcome).applyVec vector)) (vector : HilbertVector R) :
    HilbertOperator.quadraticWeight matrix vector =
      ∑ outcome, HilbertOperator.quadraticWeight (effects outcome)
        ((operators outcome).applyVec vector) := by
  apply homogeneous_of_normalized (R := R)
    (HilbertOperator.quadraticWeight matrix)
    (fun input => ∑ outcome, HilbertOperator.quadraticWeight (effects outcome)
      ((operators outcome).applyVec input))
    (quadratic_real_smul (R := R) matrix) ?_ ?_ agrees vector
  · intro scalar input
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro outcome _
    rw [HilbertOperator.applyVec_smul]
    exact quadratic_real_smul (R := R) (effects outcome) scalar
      ((operators outcome).applyVec input)
  · simp only [HilbertOperator.applyVec_zero, HilbertOperator.quadraticWeight, inner_zero_left,
      Complex.zero_re, Finset.sum_const_zero]

private lemma initial_pure_quadratic {Record : Type} [Fintype Record] {R : Register}
    (decision : DecidableEq Record) (original : Record) (vector : NormalizedVector R)
    (effects : Record → Effect R) :
    (@ExecutionState.ofValue Record _ R decision original
      (DensityOperator.ofPure vector)).effectWeight effects =
        HilbertOperator.quadraticWeight (effects original).matrix vector.vec :=
  (ExecutionState.effectWeight_ofValue_decision decision original
    (DensityOperator.ofPure vector) effects).trans (Effect.weight_ofPure _ vector)

private lemma retained_trace_sum_two {Original First Last Result : Type}
    [Fintype Original] [Fintype First] [Fintype Last] [Fintype Result]
    [DecidableEq Result] {R : Register} (record : Original → First → Last → Result)
    (blocks : Result → HilbertOperator R)
    (parts : Original → First → Last → HilbertOperator R)
    (actual : ∀ result, blocks result = ∑ original, ∑ first, ∑ last,
      if record original first last = result then parts original first last else 0)
    (effects : Result → Effect R) :
    (∑ result, ((effects result).matrix * blocks result).trace.re) =
      ∑ original, ∑ first, ∑ last,
        ((effects (record original first last)).matrix * parts original first last).trace.re := by
  let pairedRecord : Original → First × Last → Result :=
    fun original outcome => record original outcome.1 outcome.2
  let pairedParts : Original → First × Last → HilbertOperator R :=
    fun original outcome => parts original outcome.1 outcome.2
  have paired (result : Result) : blocks result = ∑ original, ∑ outcome : First × Last,
      if pairedRecord original outcome = result then pairedParts original outcome else 0 := by
    refine (actual result).trans ?_
    apply Finset.sum_congr rfl
    intro original _
    rw [Fintype.sum_prod_type]
  refine (retained_trace_sum pairedRecord blocks pairedParts paired effects).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  rw [Fintype.sum_prod_type]

private lemma retained_effectWeight_two {Original First Last Result : Type}
    [Fintype Original] [Fintype First] [Fintype Last] [Fintype Result]
    [DecidableEq Result] {R : Register}
    (initial : ExecutionState Original R) (finished : ExecutionState Result R)
    (record : Original → First → Last → Result)
    (operators : Original → First → Last → HilbertOperator R)
    (blocks : ∀ result, (finished.block result).matrix = ∑ original, ∑ first, ∑ last,
      if record original first last = result then
        operators original first last * (initial.block original).matrix *
          (operators original first last).conjTranspose else 0)
    (effects : Result → Effect R) :
    finished.effectWeight effects = ∑ original, ∑ first, ∑ last,
      ((effects (record original first last)).matrix *
        (operators original first last * (initial.block original).matrix *
          (operators original first last).conjTranspose)).trace.re := by
  unfold ExecutionState.effectWeight Effect.weight
  exact retained_trace_sum_two record (fun result => (finished.block result).matrix)
    (fun original first last => operators original first last * (initial.block original).matrix *
      (operators original first last).conjTranspose) blocks effects

private lemma initial_pure_sum_two {Original First Last Result : Type}
    [Fintype Original] [Fintype First] [Fintype Last] {R : Register}
    (decision : DecidableEq Original) (original : Original) (vector : NormalizedVector R)
    (record : Original → First → Last → Result)
    (operators : Original → First → Last → HilbertOperator R)
    (effects : Result → Effect R) :
    (∑ incoming, ∑ first, ∑ last,
      ((effects (record incoming first last)).matrix *
        (operators incoming first last *
          ((@ExecutionState.ofValue Original _ R decision original
            (DensityOperator.ofPure vector)).block incoming).matrix *
          (operators incoming first last).conjTranspose)).trace.re) =
      ∑ first, ∑ last,
        HilbertOperator.quadraticWeight (effects (record original first last)).matrix
          ((operators original first last).applyVec vector) := by
  rw [Finset.sum_eq_single original]
  · apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro last _
    simp only [ExecutionState.ofValue_block, if_true]
    exact weighted_sandwich_pure _ _ vector
  · intro other _ different
    apply Finset.sum_eq_zero
    intro first _
    apply Finset.sum_eq_zero
    intro last _
    simp only [ExecutionState.ofValue_block, if_neg different, DensityOperator.zero_matrix,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
  · intro absent
    exact (absent (Finset.mem_univ _)).elim

private lemma retained_quadratic_pure_two {Original First Last Result : Type}
    [Fintype Original] [Fintype First] [Fintype Last] [Fintype Result]
    [DecidableEq Result] {R : Register}
    (decision : DecidableEq Original)
    (transition : ExecutionState Original R → ExecutionState Result R)
    (record : Original → First → Last → Result)
    (operators : Original → First → Last → HilbertOperator R)
    (effects : Result → Effect R) (pulled : Original → Effect R)
    (blocks : ∀ state result, ((transition state).block result).matrix =
      ∑ original, ∑ first, ∑ last,
        if record original first last = result then
          operators original first last * (state.block original).matrix *
            (operators original first last).conjTranspose else 0)
    (weight : ∀ state, (transition state).effectWeight effects = state.effectWeight pulled)
    (original : Original) (vector : NormalizedVector R) :
    HilbertOperator.quadraticWeight (pulled original).matrix vector =
      ∑ first, ∑ last,
        HilbertOperator.quadraticWeight (effects (record original first last)).matrix
          ((operators original first last).applyVec vector) := by
  let initial := @ExecutionState.ofValue Original _ R decision original
    (DensityOperator.ofPure vector)
  exact (initial_pure_quadratic decision original vector pulled).symm.trans
    ((weight initial).symm.trans
      ((retained_effectWeight_two initial (transition initial) record operators
        (blocks initial) effects).trans
          (initial_pure_sum_two decision original vector record operators effects)))

private lemma quadratic_sum_two_of_normalized {R : Register} {First Last : Type}
    [Fintype First] [Fintype Last] (matrix : HilbertOperator R)
    (effects operators : First → Last → HilbertOperator R)
    (agrees : ∀ vector : NormalizedVector R,
      HilbertOperator.quadraticWeight matrix vector = ∑ first, ∑ last,
        HilbertOperator.quadraticWeight (effects first last)
          ((operators first last).applyVec vector)) (vector : HilbertVector R) :
    HilbertOperator.quadraticWeight matrix vector = ∑ first, ∑ last,
      HilbertOperator.quadraticWeight (effects first last)
        ((operators first last).applyVec vector) := by
  have pure (input : NormalizedVector R) :
      HilbertOperator.quadraticWeight matrix input = ∑ outcome : First × Last,
        HilbertOperator.quadraticWeight (effects outcome.1 outcome.2)
          ((operators outcome.1 outcome.2).applyVec input) :=
    (agrees input).trans (by rw [Fintype.sum_prod_type])
  exact (quadratic_sum_of_normalized matrix
    (fun outcome : First × Last => effects outcome.1 outcome.2)
    (fun outcome : First × Last => operators outcome.1 outcome.2) pure vector).trans
      (by rw [Fintype.sum_prod_type])

end

end QuantumAlg.Execution
