/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Operator norm on finite-register Hilbert operators

`HilbertOperator R` is an abbreviation for ordinary `Matrix`, where Mathlib
deliberately avoids choosing a default norm. `HilbertOperator.opNorm` fixes the
L2 operator norm as one plain real-valued function, so downstream statements
(approximate circuit realizations, product-formula error bounds, compiled
circuit error composition) never install a global matrix norm instance. Proofs
open the scoped `Matrix.Norms.L2Operator` instances locally and export only
norm facts about the plain function.

The unitary-invariance and telescoping lemmas are the two facts every error
composition argument in the library reduces to: multiplying by a unitary does
not change the norm, and `‖U₁ U₂ - V₁ V₂‖ ≤ ‖U₁ - V₁‖ + ‖U₂ - V₂‖` when
`U₂` and `V₁` are unitary.
-/

@[expose] public section

namespace QuantumAlg

namespace HilbertOperator

noncomputable section

variable {R : Register}

/-- The L2 operator norm of a raw finite-register Hilbert operator. -/
def opNorm (A : HilbertOperator R) : ℝ :=
  open scoped Matrix.Norms.L2Operator in
  ‖A‖

@[simp]
theorem opNorm_zero : opNorm (0 : HilbertOperator R) = 0 := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_zero

theorem opNorm_nonneg (A : HilbertOperator R) : 0 ≤ opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_nonneg A

theorem opNorm_eq_zero_iff {A : HilbertOperator R} : opNorm A = 0 ↔ A = 0 := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_eq_zero

@[simp]
theorem opNorm_neg (A : HilbertOperator R) : opNorm (-A) = opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_neg A

theorem opNorm_add_le (A B : HilbertOperator R) :
    opNorm (A + B) ≤ opNorm A + opNorm B := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_add_le A B

theorem opNorm_sub_le (A B : HilbertOperator R) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_sub_le A B

theorem opNorm_sub_comm (A B : HilbertOperator R) :
    opNorm (A - B) = opNorm (B - A) := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_sub_rev A B

/-- Triangle inequality in difference form. -/
theorem opNorm_sub_le_add (A B C : HilbertOperator R) :
    opNorm (A - C) ≤ opNorm (A - B) + opNorm (B - C) := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_sub_le_norm_sub_add_norm_sub A B C

theorem opNorm_sum_le {ι : Type} [Fintype ι] (f : ι → HilbertOperator R) :
    opNorm (∑ i, f i) ≤ ∑ i, opNorm (f i) := by
  classical
  let s : Finset ι := Finset.univ
  change opNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, opNorm (f i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (opNorm_add_le _ _).trans (add_le_add_right ih _)

theorem opNorm_smul (c : ℂ) (A : HilbertOperator R) :
    opNorm (c • A) = ‖c‖ * opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_smul c A

theorem opNorm_star (A : HilbertOperator R) : opNorm (star A) = opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_star A

theorem opNorm_conjTranspose (A : HilbertOperator R) :
    opNorm A.conjTranspose = opNorm A := by
  rw [← Matrix.star_eq_conjTranspose]
  exact opNorm_star A

theorem opNorm_one [Nonempty R.Index] : opNorm (1 : HilbertOperator R) = 1 := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact norm_one

theorem opNorm_mul_le (A B : HilbertOperator R) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact Matrix.l2_opNorm_mul A B

/-- The operator norm bounds the action on raw vectors, stated on the
underlying `mulVec`. -/
theorem opNorm_mulVec_le (A : HilbertOperator R) (ψ : HilbertVector R) :
    ‖WithLp.toLp 2 (A.mulVec ψ.ofLp)‖ ≤ opNorm A * ‖ψ‖ := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact Matrix.l2_opNorm_mulVec A ψ

/-! ## Unitary invariance -/

theorem opNorm_of_mem_unitaryGroup [Nonempty R.Index] {U : HilbertOperator R}
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) : opNorm U = 1 := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact CStarRing.norm_of_mem_unitary hU

theorem opNorm_unitaryGroup_mul {U : HilbertOperator R} (A : HilbertOperator R)
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) : opNorm (U * A) = opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact CStarRing.norm_mem_unitary_mul A hU

theorem opNorm_mul_unitaryGroup {U : HilbertOperator R} (A : HilbertOperator R)
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) : opNorm (A * U) = opNorm A := by
  unfold opNorm
  open scoped Matrix.Norms.L2Operator in
  exact CStarRing.norm_mul_mem_unitary A hU

/-- A unitary operator has operator norm one. -/
theorem opNorm_unitary [Nonempty R.Index] (U : UnitaryOperator R) :
    opNorm (U : HilbertOperator R) = 1 :=
  opNorm_of_mem_unitaryGroup U.2

/-- Left multiplication by a unitary operator preserves the operator norm. -/
theorem opNorm_unitary_mul_left (U : UnitaryOperator R) (A : HilbertOperator R) :
    opNorm ((U : HilbertOperator R) * A) = opNorm A :=
  opNorm_unitaryGroup_mul A U.2

/-- Right multiplication by a unitary operator preserves the operator norm. -/
theorem opNorm_unitary_mul_right (A : HilbertOperator R) (U : UnitaryOperator R) :
    opNorm (A * (U : HilbertOperator R)) = opNorm A :=
  opNorm_mul_unitaryGroup A U.2

/-- The distance between two unitaries is at most two. -/
theorem opNorm_unitary_sub_unitary_le [Nonempty R.Index] (U V : UnitaryOperator R) :
    opNorm ((U : HilbertOperator R) - (V : HilbertOperator R)) ≤ 2 := by
  calc opNorm ((U : HilbertOperator R) - (V : HilbertOperator R))
      ≤ opNorm (U : HilbertOperator R) + opNorm (V : HilbertOperator R) := opNorm_sub_le _ _
    _ = 2 := by rw [opNorm_unitary, opNorm_unitary]; norm_num

/-! ## Telescoping -/

/-- Telescoping bound for a product of two factors: the error of a product is at
most the sum of the factor errors, provided `A₂` and `B₁` are unitary. -/
theorem opNorm_mul_sub_mul_le {A₁ A₂ B₁ B₂ : HilbertOperator R}
    (hA₂ : A₂ ∈ Matrix.unitaryGroup R.Index ℂ)
    (hB₁ : B₁ ∈ Matrix.unitaryGroup R.Index ℂ) :
    opNorm (A₁ * A₂ - B₁ * B₂) ≤ opNorm (A₁ - B₁) + opNorm (A₂ - B₂) := by
  have hsplit : A₁ * A₂ - B₁ * B₂ = (A₁ - B₁) * A₂ + B₁ * (A₂ - B₂) := by
    noncomm_ring
  rw [hsplit]
  calc opNorm ((A₁ - B₁) * A₂ + B₁ * (A₂ - B₂))
      ≤ opNorm ((A₁ - B₁) * A₂) + opNorm (B₁ * (A₂ - B₂)) := opNorm_add_le _ _
    _ = opNorm (A₁ - B₁) + opNorm (A₂ - B₂) := by
        rw [opNorm_mul_unitaryGroup _ hA₂, opNorm_unitaryGroup_mul _ hB₁]

/-- Telescoping bound stated on certified unitary operators. -/
theorem opNorm_unitary_mul_sub_mul_le (U₁ U₂ V₁ V₂ : UnitaryOperator R) :
    opNorm (((U₁ * U₂ : UnitaryOperator R) : HilbertOperator R) -
        ((V₁ * V₂ : UnitaryOperator R) : HilbertOperator R)) ≤
      opNorm ((U₁ : HilbertOperator R) - (V₁ : HilbertOperator R)) +
        opNorm ((U₂ : HilbertOperator R) - (V₂ : HilbertOperator R)) :=
  opNorm_mul_sub_mul_le (A₁ := (U₁ : HilbertOperator R)) (A₂ := (U₂ : HilbertOperator R))
    (B₁ := (V₁ : HilbertOperator R)) (B₂ := (V₂ : HilbertOperator R)) U₂.2 V₁.2

/-- Repeated telescoping: `‖U^n - V^n‖ ≤ n * ‖U - V‖` for unitaries. -/
theorem opNorm_pow_sub_pow_le {U V : HilbertOperator R}
    (hU : U ∈ Matrix.unitaryGroup R.Index ℂ) (hV : V ∈ Matrix.unitaryGroup R.Index ℂ) (n : ℕ) :
    opNorm (U ^ n - V ^ n) ≤ n * opNorm (U - V) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hVn : V ^ n ∈ Matrix.unitaryGroup R.Index ℂ := pow_mem hV n
      have hstep : opNorm (U ^ n * U - V ^ n * V) ≤ opNorm (U ^ n - V ^ n) + opNorm (U - V) :=
        opNorm_mul_sub_mul_le (A₁ := U ^ n) (A₂ := U) (B₁ := V ^ n) (B₂ := V) hU hVn
      rw [pow_succ, pow_succ]
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [hstep, ih]

end

end HilbertOperator

end QuantumAlg

end

/-!
## Vector action

`HilbertOperator.applyVec` is module-private in `Gate/Basic`, so the bound on the
vector action is exported at the same visibility: downstream modules reach it
through `import all QuantumAlg.Core.Base.Gate.OperatorNorm`.
-/

section

namespace QuantumAlg.HilbertOperator

variable {R : Register}

/-- The operator norm bounds the action on raw state vectors. -/
theorem norm_applyVec_le (A : HilbertOperator R) (ψ : HilbertVector R) :
    ‖applyVec A ψ‖ ≤ opNorm A * ‖ψ‖ :=
  opNorm_mulVec_le A ψ

end QuantumAlg.HilbertOperator

end
