/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Gate.Effect
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Positive contractive effects pulled back through rectangular isometries

The columns are arbitrary complex amplitudes between two finite registers.
Their Gram identity certifies the full source space, including an empty source
index type. This mathematical construction neither allocates a register nor
supplies the Gram identity for an actual circuit. Concrete instrument
completeness remains a separate internal proof obligation.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.EffectPullback

noncomputable section

open QuantumAlg
open scoped ComplexOrder

variable {Source Target : Register}

/-- The column Gram identity is the left-inverse identity for the Euclidean adjoint. -/
lemma columns_adjoint_comp
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1) :
    columns.toEuclideanLin.adjoint.comp columns.toEuclideanLin = LinearMap.id := by
  calc
    columns.toEuclideanLin.adjoint.comp columns.toEuclideanLin =
        (columns.conjTranspose * columns).toEuclideanLin := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      exact (Matrix.toLpLin_mul_same 2 columns.conjTranspose columns).symm
    _ = (1 : Matrix Source.Index Source.Index ℂ).toEuclideanLin :=
      congrArg Matrix.toEuclideanLin complete
    _ = LinearMap.id := Matrix.toLpLin_one 2

/-- All source vectors retain their norm under the same rectangular columns. -/
lemma columns_norm
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1)
    (vector : HilbertVector Source) :
    ‖columns.toEuclideanLin vector‖ = ‖vector‖ := by
  have inner_preserved : ∀ left right : HilbertVector Source,
      inner ℂ (columns.toEuclideanLin left) (columns.toEuclideanLin right) =
        inner ℂ left right := by
    intro left right
    rw [← LinearMap.adjoint_inner_right columns.toEuclideanLin]
    have returned := congrArg
      (fun operator : HilbertVector Source →ₗ[ℂ] HilbertVector Source => operator right)
      (columns_adjoint_comp columns complete)
    change columns.toEuclideanLin.adjoint (columns.toEuclideanLin right) = right at returned
    rw [returned]
  exact (LinearMap.norm_map_iff_inner_map_map columns.toEuclideanLin).mpr
    inner_preserved vector

/-- The adjoint of the same rectangular isometry is contractive on every target vector. -/
lemma adjoint_columns_norm_le
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1)
    (vector : HilbertVector Target) :
    ‖columns.conjTranspose.toEuclideanLin vector‖ ≤ ‖vector‖ := by
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have bounded := re_inner_le_norm (𝕜 := ℂ)
    (columns.toEuclideanLin (columns.toEuclideanLin.adjoint vector)) vector
  rw [← LinearMap.adjoint_inner_right columns.toEuclideanLin,
    inner_self_eq_norm_sq_to_K] at bounded
  simp only [RCLike.re_ofReal_pow] at bounded
  rw [columns_norm columns complete] at bounded
  by_cases vanish : ‖columns.toEuclideanLin.adjoint vector‖ = 0
  · rw [vanish]
    exact norm_nonneg vector
  · have positive : 0 < ‖columns.toEuclideanLin.adjoint vector‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm vanish)
    exact _root_.le_of_mul_le_mul_left (by simpa only [pow_two] using bounded) positive

/-- Pull any target effect back through amplitudes certified on the complete source space. -/
def pullbackEffect
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1)
    (effect : Effect Target) : Effect Source where
  matrix := columns.conjTranspose * effect.matrix * columns
  positive := effect.positive.conjTranspose_mul_mul_same columns
  contractive vector := by
    change ‖Matrix.toLpLin 2 2 (columns.conjTranspose * effect.matrix * columns) vector‖ ≤ _
    rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_mul_same]
    change ‖columns.conjTranspose.toEuclideanLin
      (effect.matrix.applyVec (columns.toEuclideanLin vector))‖ ≤ ‖vector‖
    exact (adjoint_columns_norm_le columns complete _).trans
      ((effect.contractive (columns.toEuclideanLin vector)).trans_eq
        (columns_norm columns complete vector))

/-- The pulled effect has the literal rectangular conjugation matrix. -/
lemma pullbackEffect_matrix
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1)
    (effect : Effect Target) :
    (pullbackEffect columns complete effect).matrix =
      columns.conjTranspose * effect.matrix * columns := rfl

/-- The pullback weight equals the target trace pairing for every mixed source density. -/
lemma pullbackEffect_weight
    (columns : Matrix Target.Index Source.Index ℂ)
    (complete : columns.conjTranspose * columns = 1)
    (effect : Effect Target) (state : DensityOperator Source) :
    (pullbackEffect columns complete effect).weight state =
      (effect.matrix * (columns * state.matrix * columns.conjTranspose)).trace.re := by
  unfold Effect.weight pullbackEffect
  congr 1
  calc
    ((columns.conjTranspose * effect.matrix * columns) * state.matrix).trace =
        (columns.conjTranspose * (effect.matrix * (columns * state.matrix))).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((effect.matrix * (columns * state.matrix)) * columns.conjTranspose).trace :=
      Matrix.trace_mul_comm _ _
    _ = (effect.matrix * (columns * state.matrix * columns.conjTranspose)).trace := by
      simp only [Matrix.mul_assoc]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.EffectPullback
