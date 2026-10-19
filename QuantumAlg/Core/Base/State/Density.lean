/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Register
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic

/-!
# Finite-dimensional subnormalized quantum states

`DensityOperator` carries positivity and a trace at most one. Its trace records
the mass of an execution branch; zero-mass branches remain zero and are never
assigned an artificial normalized state. Normalization is an explicit predicate.

The pure-state embedding and unitary action follow [dW19, qcnotes.tex:5381]
and [dW19, qcnotes.tex:5400]. Subnormalization extends the same matrix semantics
to individual measurement branches without dividing by their probability.
-/

@[expose] public section

open scoped ComplexOrder

namespace QuantumAlg

/-- A positive quantum operator with mass at most one.

Trace-one operators are density matrices [dW19, qcnotes.tex:5394]; allowing
smaller trace retains the probability weight of a measurement branch. -/
structure DensityOperator (R : Register) where
  /-- Matrix on exactly the advertised finite register. -/
  matrix : HilbertOperator R
  /-- Positivity includes Hermitian symmetry. -/
  positive : matrix.PosSemidef
  /-- The total branch probability is at most one. -/
  trace_le_one : matrix.trace.re ≤ 1

namespace DensityOperator

noncomputable section

variable {R S : Register}

/-- Probability mass retained by the state. -/
def mass (ρ : DensityOperator R) : ℝ := ρ.matrix.trace.re

/-- A state is normalized exactly when its branch has total mass one. -/
def IsNormalized (ρ : DensityOperator R) : Prop := ρ.mass = 1

/-- Positive matrices have nonnegative real trace. -/
lemma mass_nonneg (ρ : DensityOperator R) : 0 ≤ ρ.mass :=
  (Complex.nonneg_iff.mp ρ.positive.trace_nonneg).1

/-- Every represented execution branch has mass at most one. -/
lemma mass_le_one (ρ : DensityOperator R) : ρ.mass ≤ 1 := ρ.trace_le_one

/-- The trace has no imaginary component. -/
lemma trace_im_eq_zero (ρ : DensityOperator R) : ρ.matrix.trace.im = 0 :=
  (Complex.nonneg_iff.mp ρ.positive.trace_nonneg).2.symm

@[ext]
lemma ext {ρ σ : DensityOperator R} (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- The impossible branch, represented without normalization. -/
def zero (R : Register) : DensityOperator R where
  matrix := 0
  positive := Matrix.PosSemidef.zero
  trace_le_one := by simp

@[simp] lemma zero_matrix : (zero R).matrix = 0 := rfl

@[simp] lemma zero_mass : (zero R).mass = 0 := by simp [mass, zero]

/-- A zero-probability branch has the zero operator, not an arbitrary
normalized state. -/
lemma eq_zero_of_mass_eq_zero (ρ : DensityOperator R) (h : ρ.mass = 0) :
    ρ = zero R := by
  apply ext
  apply ρ.positive.trace_eq_zero_iff.mp
  exact Complex.ext h ρ.trace_im_eq_zero

/-- Trace of the pure-state outer product [dW19, qcnotes.tex:5381]. -/
lemma trace_pureMatrix (ψ : NormalizedVector R) :
    (Matrix.vecMulVec (fun i => ψ i) (fun i => star (ψ i))).trace = 1 := by
  have hnorm : inner ℂ (ψ : HilbertVector R) (ψ : HilbertVector R) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, ψ.norm_eq_one]
    norm_num
  change (∑ i, ψ i * star (ψ i)) = 1
  simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply] using hnorm

/-- Rank-one embedding of a pure state [dW19, qcnotes.tex:5381]. -/
def ofPure (ψ : NormalizedVector R) : DensityOperator R where
  matrix := Matrix.vecMulVec (fun i => ψ i) (fun i => star (ψ i))
  positive := Matrix.posSemidef_vecMulVec_self_star (fun i => ψ i)
  trace_le_one := by rw [trace_pureMatrix]; exact le_rfl

@[simp] lemma ofPure_matrix (ψ : NormalizedVector R) (i j : R.Index) :
    (ofPure ψ).matrix i j = ψ i * star (ψ j) := rfl

/-- The rank-one embedding retains normalization. -/
lemma ofPure_normalized (ψ : NormalizedVector R) : (ofPure ψ).IsNormalized := by
  change (Matrix.vecMulVec (fun i => ψ i) (fun i => star (ψ i))).trace.re = 1
  rw [trace_pureMatrix]
  rfl

/-- Unitary conjugation preserves trace [dW19, qcnotes.tex:5405]. -/
lemma trace_unitary_conjugation (U : UnitaryOperator R) (A : HilbertOperator R) :
    ((U : HilbertOperator R) * A * (U : HilbertOperator R).conjTranspose).trace =
      A.trace := by
  rw [Matrix.trace_mul_cycle]
  have hU : (U : HilbertOperator R).conjTranspose * (U : HilbertOperator R) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  rw [hU, Matrix.one_mul]

/-- The unitary action on a mixed state [dW19, qcnotes.tex:5405]. -/
def applyUnitary (U : UnitaryOperator R) (ρ : DensityOperator R) : DensityOperator R where
  matrix := (U : HilbertOperator R) * ρ.matrix * (U : HilbertOperator R).conjTranspose
  positive := ρ.positive.mul_mul_conjTranspose_same (U : HilbertOperator R)
  trace_le_one := by rw [trace_unitary_conjugation]; exact ρ.trace_le_one

@[simp] lemma applyUnitary_matrix (U : UnitaryOperator R) (ρ : DensityOperator R) :
    (applyUnitary U ρ).matrix =
      (U : HilbertOperator R) * ρ.matrix * (U : HilbertOperator R).conjTranspose := rfl

@[simp] lemma applyUnitary_mass (U : UnitaryOperator R) (ρ : DensityOperator R) :
    (applyUnitary U ρ).mass = ρ.mass := by
  simp only [mass, applyUnitary_matrix, trace_unitary_conjugation]

/-- Quantum evolution preserves the normalized-state predicate. -/
lemma applyUnitary_normalized (U : UnitaryOperator R) (ρ : DensityOperator R)
    (hρ : ρ.IsNormalized) : (applyUnitary U ρ).IsNormalized := by
  simpa only [IsNormalized, applyUnitary_mass] using hρ

@[simp] lemma applyUnitary_one (ρ : DensityOperator R) : applyUnitary 1 ρ = ρ := by
  apply ext
  simp [applyUnitary]

/-- Sequential unitary action agrees with multiplication in the original
certified unitary group. -/
lemma applyUnitary_mul (U V : UnitaryOperator R) (ρ : DensityOperator R) :
    applyUnitary (U * V) ρ = applyUnitary U (applyUnitary V ρ) := by
  apply ext
  simp [applyUnitary, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The mixed-state interpreter extends the original exact pure-state action
[dW19, qcnotes.tex:5400]. -/
public lemma ofPure_apply (U : UnitaryOperator R) (ψ : NormalizedVector R) :
    ofPure (U.apply ψ) = applyUnitary U (ofPure ψ) := by
  apply ext
  ext i j
  change (∑ a, U i a * ψ a) * star (∑ b, U j b * ψ b) =
    ∑ b, (∑ a, U i a * (ψ a * star (ψ b))) * star (U j b)
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Forget the right subsystem's state while retaining the left marginal.
This mathematical operation alone does not release physical storage. -/
def marginalLeft (ρ : DensityOperator (Register.prod R S)) : DensityOperator R where
  matrix := ∑ j : S.Index, ρ.matrix.submatrix (fun i => (i, j)) (fun i => (i, j))
  positive := Matrix.posSemidef_sum _ (fun j _ => ρ.positive.submatrix (fun i => (i, j)))
  trace_le_one := by
    have htrace :
        (∑ j : S.Index, ρ.matrix.submatrix (fun i => (i, j))
          (fun i => (i, j))).trace = ρ.matrix.trace := by
      simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply, Matrix.submatrix_apply]
      exact (Fintype.sum_prod_type (fun ij : R.Index × S.Index =>
        ρ.matrix ij ij)).symm
    rw [htrace]
    exact ρ.trace_le_one

@[simp] lemma marginalLeft_matrix (ρ : DensityOperator (Register.prod R S))
    (i k : R.Index) :
    (marginalLeft ρ).matrix i k = ∑ j : S.Index, ρ.matrix (i, j) (k, j) := by
  simp [marginalLeft, Matrix.sum_apply, Matrix.submatrix_apply]

/-- Taking a marginal preserves branch mass. -/
lemma marginalLeft_mass (ρ : DensityOperator (Register.prod R S)) :
    (marginalLeft ρ).mass = ρ.mass := by
  unfold mass
  congr 1
  simp only [Matrix.trace, Matrix.diag, marginalLeft_matrix]
  exact (Fintype.sum_prod_type (fun ij : R.Index × S.Index => ρ.matrix ij ij)).symm

end

end DensityOperator

end QuantumAlg
