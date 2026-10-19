/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.EffectPullback
import all QuantumAlg.Core.Base.Gate.Effect
import Mathlib.Data.Fintype.BigOperators

/-!
# Complete finite Kraus families and selected positive contractive effects

The outcome register is a mathematical coordinate space. Stacking a Kraus
family keeps every outcome as a separate row label; it never adds amplitudes
across distinct outcomes. A predicate may select any full outcome label,
including path, Store, and frequency coordinates carried by that label.

The complete family Gram identity is a generic mathematical hypothesis. Its
proof for the actual point instrument remains a separate internal obligation.
No runtime allocation, physical source register, clean-input condition,
reference restriction, or algorithm caller premise is introduced here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.KrausEffects

noncomputable section

open QuantumAlg
open scoped BigOperators ComplexOrder

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {Source Target : Register} {Outcome : Type}

/-- Mathematical rows retain both the complete outcome and the target basis coordinate. -/
abbrev outcomeRegister (Outcome : Type) [Fintype Outcome] [DecidableEq Outcome]
    (Target : Register) : Register where
  Index := Outcome × Target.Index
  fintype := inferInstance
  decEq := inferInstance

/-- Distinct Kraus labels become distinct rows, with their literal amplitudes unchanged. -/
def stackedColumns [Fintype Outcome] [DecidableEq Outcome]
    (kernels : Outcome → Matrix Target.Index Source.Index ℂ) :
    Matrix (outcomeRegister Outcome Target).Index Source.Index ℂ :=
  fun output input => kernels output.1 output.2 input

/-- The stacked column Gram is exactly the CP family's sum of individual Grams. -/
lemma stackedColumns_gram [Fintype Outcome] [DecidableEq Outcome]
    (kernels : Outcome → Matrix Target.Index Source.Index ℂ) :
    (stackedColumns kernels).conjTranspose * stackedColumns kernels =
      ∑ outcome, (kernels outcome).conjTranspose * kernels outcome := by
  ext row column
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stackedColumns,
    Matrix.sum_apply, Fintype.sum_prod_type]

/-- The diagonal matrix retains exactly the selected basis coordinates. -/
def basisPredicateMatrix (R : Register) (selected : R.Index → Prop) : HilbertOperator R :=
  Matrix.diagonal fun index => if selected index then 1 else 0

/-- Predicate selection is pointwise multiplication by the same zero/one diagonal. -/
lemma basisPredicateMatrix_applyVec (R : Register) (selected : R.Index → Prop)
    (vector : HilbertVector R) (index : R.Index) :
    (basisPredicateMatrix R selected).applyVec vector index =
      if selected index then vector index else 0 := by
  change ((Matrix.diagonal _).mulVec vector.ofLp) index = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp_all

/-- Every basis predicate is a positive contractive effect on its full mathematical register. -/
def basisPredicateEffect (R : Register) (selected : R.Index → Prop) : Effect R where
  matrix := basisPredicateMatrix R selected
  positive := by
    change (Matrix.diagonal
      (fun index : R.Index => if selected index then (1 : ℂ) else 0)).PosSemidef
    apply Matrix.PosSemidef.diagonal
    intro index
    change (0 : ℂ) ≤ if selected index then 1 else 0
    split_ifs <;> simp
  contractive vector := by
    have bound : ‖(basisPredicateMatrix R selected).applyVec vector‖ ^ 2 ≤ ‖vector‖ ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, basisPredicateMatrix_applyVec]
      apply Finset.sum_le_sum
      intro index _
      split_ifs <;> simp
    nlinarith [norm_nonneg vector,
      norm_nonneg ((basisPredicateMatrix R selected).applyVec vector)]

/-- The certified effect retains the literal zero/one predicate matrix. -/
lemma basisPredicateEffect_matrix (R : Register) (selected : R.Index → Prop) :
    (basisPredicateEffect R selected).matrix =
      Matrix.diagonal (fun index => if selected index then 1 else 0) := rfl

/-- Select complete outcome labels from a complete family by a rectangular effect pullback. -/
def selectedEffect [Fintype Outcome] [DecidableEq Outcome]
    (kernels : Outcome → Matrix Target.Index Source.Index ℂ)
    (complete : ∑ outcome, (kernels outcome).conjTranspose * kernels outcome = 1)
    (selected : Outcome → Prop) : Effect Source :=
  EffectPullback.pullbackEffect (stackedColumns kernels)
    ((stackedColumns_gram kernels).trans complete)
    (basisPredicateEffect (outcomeRegister Outcome Target) (fun label => selected label.1))

/-- The selected effect is precisely the selected CP sum, with no cross-outcome amplitudes. -/
lemma selectedEffect_matrix [Fintype Outcome] [DecidableEq Outcome]
    (kernels : Outcome → Matrix Target.Index Source.Index ℂ)
    (complete : ∑ outcome, (kernels outcome).conjTranspose * kernels outcome = 1)
    (selected : Outcome → Prop) :
    (selectedEffect kernels complete selected).matrix =
      ∑ outcome, if selected outcome then
        (kernels outcome).conjTranspose * kernels outcome else 0 := by
  ext row column
  change ((stackedColumns kernels).conjTranspose *
    Matrix.diagonal (fun label : (outcomeRegister Outcome Target).Index =>
      if selected label.1 then (1 : ℂ) else 0) *
      stackedColumns kernels) row column = _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, stackedColumns,
    Matrix.sum_apply, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases chosen : selected outcome
  · simp only [if_pos chosen, mul_one, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · simp only [if_neg chosen, mul_zero, zero_mul, Finset.sum_const_zero, Matrix.zero_apply]

/-- Exact selected branch trace weight holds on every mixed source density. -/
lemma selectedEffect_weight [Fintype Outcome] [DecidableEq Outcome]
    (kernels : Outcome → Matrix Target.Index Source.Index ℂ)
    (complete : ∑ outcome, (kernels outcome).conjTranspose * kernels outcome = 1)
    (selected : Outcome → Prop) (state : DensityOperator Source) :
    (selectedEffect kernels complete selected).weight state =
      ∑ outcome, if selected outcome then
        (kernels outcome * state.matrix * (kernels outcome).conjTranspose).trace.re else 0 := by
  change ((selectedEffect kernels complete selected).matrix * state.matrix).trace.re = _
  rw [selectedEffect_matrix]
  simp only [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases chosen : selected outcome
  · simp only [if_pos chosen]
    congr 1
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  · simp only [if_neg chosen, zero_mul, Matrix.trace_zero, Complex.zero_re]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.KrausEffects
