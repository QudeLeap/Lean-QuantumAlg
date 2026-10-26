/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Core.Base.State.Normalized

/-!
# Raw Hilbert operators

`HilbertOperator R` is the unrestricted complex matrix over `R`. Observables,
projectors, block-encoding targets, sums, scalar multiples, and polynomials live at
this layer even when they are not unitary.
-/

section

namespace QuantumAlg

/-- Raw linear operator over a finite quantum register. -/
public abbrev HilbertOperator (R : Register) : Type := Matrix R.Index R.Index ℂ

namespace HilbertOperator

noncomputable section

variable {R : Register}

/-- Matrix-vector multiplication on raw state vectors. -/
def applyVec (A : HilbertOperator R) (ψ : HilbertVector R) : HilbertVector R :=
  WithLp.toLp 2 (A.mulVec ψ.ofLp)

@[simp]
lemma applyVec_apply (A : HilbertOperator R) (ψ : HilbertVector R) (i : R.Index) :
    applyVec A ψ i = ∑ j, A i j * ψ j := rfl

/-- Every linear Hilbert operator annihilates the zero vector. -/
lemma applyVec_zero (matrix : HilbertOperator R) :
    matrix.applyVec 0 = 0 := by
  ext index
  simp [HilbertOperator.applyVec_apply]

@[simp]
lemma applyVec_add (A : HilbertOperator R) (ψ φ : HilbertVector R) :
    applyVec A (ψ + φ) = applyVec A ψ + applyVec A φ := by
  unfold applyVec
  rw [show (ψ + φ).ofLp = ψ.ofLp + φ.ofLp from rfl, Matrix.mulVec_add]
  rfl

@[simp]
lemma applyVec_sub (A : HilbertOperator R) (ψ φ : HilbertVector R) :
    applyVec A (ψ - φ) = applyVec A ψ - applyVec A φ := by
  unfold applyVec
  rw [show (ψ - φ).ofLp = ψ.ofLp - φ.ofLp from rfl, Matrix.mulVec_sub]
  rfl

@[simp]
lemma applyVec_smul (A : HilbertOperator R) (c : ℂ) (ψ : HilbertVector R) :
    applyVec A (c • ψ) = c • applyVec A ψ := by
  unfold applyVec
  rw [show (c • ψ).ofLp = c • ψ.ofLp from rfl, Matrix.mulVec_smul]
  rfl

@[simp]
lemma applyVec_neg (A : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec A (-ψ) = -applyVec A ψ := by
  unfold applyVec
  rw [show (-ψ).ofLp = -ψ.ofLp from rfl, Matrix.mulVec_neg]
  rfl

@[simp]
lemma add_applyVec (A B : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (A + B) ψ = applyVec A ψ + applyVec B ψ := by
  unfold applyVec
  rw [Matrix.add_mulVec]
  rfl

@[simp]
lemma sub_applyVec (A B : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (A - B) ψ = applyVec A ψ - applyVec B ψ := by
  unfold applyVec
  rw [Matrix.sub_mulVec]
  rfl

@[simp]
lemma smul_applyVec (c : ℂ) (A : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (c • A) ψ = c • applyVec A ψ := by
  unfold applyVec
  rw [Matrix.smul_mulVec]
  rfl

@[simp]
lemma one_applyVec (ψ : HilbertVector R) : applyVec (1 : HilbertOperator R) ψ = ψ := by
  unfold applyVec
  rw [Matrix.one_mulVec]

lemma mul_applyVec (A B : HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (A * B) ψ = applyVec A (applyVec B ψ) := by
  unfold applyVec
  rw [show (WithLp.toLp 2 (B.mulVec ψ.ofLp)).ofLp = B.mulVec ψ.ofLp from rfl,
    Matrix.mulVec_mulVec]

/-- Applying an operator to a basis ket selects its corresponding column. -/
lemma applyVec_ket (A : HilbertOperator R) (x : R.Index) (i : R.Index) :
    applyVec A (NormalizedVector.ket x : HilbertVector R) i = A i x := by
  rw [applyVec_apply]
  simp only [NormalizedVector.ket_apply, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' x (fun j => A i j)

/-- Hilbert operators are equal when they agree on all state vectors. -/
lemma ext_of_applyVec_eq {A B : HilbertOperator R}
    (h : ∀ ψ : HilbertVector R, applyVec A ψ = applyVec B ψ) : A = B := by
  ext i j
  have hket := congrArg (fun ψ : HilbertVector R => ψ i)
    (h (NormalizedVector.ket j : HilbertVector R))
  simpa using hket

lemma applyVec_sum {ι : Type} [Fintype ι]
    (A : HilbertOperator R) (f : ι → HilbertVector R) :
    applyVec A (∑ i, f i) = ∑ i, applyVec A (f i) := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · ext k
    simp [applyVec_apply]
  · intro i s hi ih
    simp [Finset.sum_insert, hi, applyVec_add, ih]

lemma sum_applyVec {ι : Type} [Fintype ι]
    (f : ι → HilbertOperator R) (ψ : HilbertVector R) :
    applyVec (∑ i, f i) ψ = ∑ i, applyVec (f i) ψ := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · ext k
    simp [applyVec_apply]
  · intro i s hi ih
    simp [Finset.sum_insert, hi, add_applyVec, ih]

lemma ext_of_applyVec_eq_on_orthonormalBasis {ι : Type} [Fintype ι]
    (basis : OrthonormalBasis ι ℂ (HilbertVector R)) {A B : HilbertOperator R}
    (h : ∀ i : ι, applyVec A (basis i) = applyVec B (basis i)) : A = B := by
  apply ext_of_applyVec_eq
  intro ψ
  calc
    applyVec A ψ = applyVec A (∑ i, basis.repr ψ i • basis i) := by rw [basis.sum_repr]
    _ = ∑ i, applyVec A (basis.repr ψ i • basis i) := by rw [applyVec_sum]
    _ = ∑ i, basis.repr ψ i • applyVec A (basis i) := by simp [applyVec_smul]
    _ = ∑ i, basis.repr ψ i • applyVec B (basis i) := by
      exact Finset.sum_congr rfl fun i _ => by rw [h i]
    _ = ∑ i, applyVec B (basis.repr ψ i • basis i) := by simp [applyVec_smul]
    _ = applyVec B (∑ i, basis.repr ψ i • basis i) := by rw [applyVec_sum]
    _ = applyVec B ψ := by rw [basis.sum_repr]

end

end HilbertOperator

end QuantumAlg

end
