/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.AdModule

/-!
# Lie-invariance of the quadratic Casimir `[H, C] = 0`

The quadratic Casimir `C = ∑ⱼ Bⱼ ⊗ₖ Bⱼ` (over a Hilbert–Schmidt orthonormal Hermitian basis `Bⱼ`
of the dynamical Lie algebra `g`) is invariant under the **diagonal/coproduct** adjoint action of
`g` on the doubled operator space: `⁅H ⊗ₖ 1 + 1 ⊗ₖ H, C⁆ = 0`, i.e. `C ∈ adCommutantGG`.

The structural fact behind it is the **ad-invariance of the Hilbert–Schmidt form on the basis**:
`⟪Bₗ, ⁅Bᵢ, Bₖ⁆⟫ = − ⟪Bₖ, ⁅Bᵢ, Bₗ⁆⟫`. Because every `Bⱼ` is Hermitian and the HS pairing of two
Hermitian-derived brackets is computed by trace cyclicity, this antisymmetry holds with a **bare
minus sign** (no conjugation) — the Casimir cancellation is then the symmetric/antisymmetric index
swap `fᵢₖₗ = −fᵢₗₖ` against the symmetric tensor `Bₗ⊗Bₖ + Bₖ⊗Bₗ`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)}

/-- **Ad-invariance of the HS form on the basis (convention lemma).** For the Hermitian
HS-orthonormal basis `Bⱼ`, `⟪Bₗ, ⁅Bᵢ, Bₖ⁆⟫ = − ⟪Bₖ, ⁅Bᵢ, Bₗ⁆⟫`. Proved by pure trace cyclicity —
no conjugation, since all basis vectors are Hermitian. -/
theorem hsInner_bracket_antisymm (b : DLAHermBasis gens) (i k l : Fin b.dim) :
    hsInner (b.B l) ⁅b.B i, b.B k⁆ = - hsInner (b.B k) ⁅b.B i, b.B l⁆ := by
  simp only [hsInner, Ring.lie_def, b.herm, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc]
  have eA : (b.B l * b.B i * b.B k).trace = (b.B k * b.B l * b.B i).trace :=
    Matrix.trace_mul_cycle (b.B l) (b.B i) (b.B k)
  have eB : (b.B l * b.B k * b.B i).trace = (b.B k * b.B i * b.B l).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm (b.B l) (b.B k * b.B i)]
  rw [eA, eB]; ring

/-- **`gProj` fixes the algebra.** The HS projection `gProj = ∑ⱼ ⟪Bⱼ,·⟫ • Bⱼ` is the identity on
`g`, since `{Bⱼ}` is an orthonormal basis of `g`. -/
theorem gProj_eq_self_of_mem (b : DLAHermBasis gens) {v : Matrix (Fin N) (Fin N) ℂ}
    (hv : v ∈ (dynamicalLieAlgebra gens).toSubmodule) : b.gProj v = v := by
  rw [← b.span_eq] at hv
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have key : ∀ j, hsInner (b.B j) (∑ i, c i • b.B i) = c j := fun j => by
    simp only [hsInner_sum_right, hsInner_smul_right, b.ortho, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ∑ j, hsInner (b.B j) (∑ i, c i • b.B i) • b.B j = _
  simp only [key]

/-- `⊗ₖ` distributes over negation on the left. -/
theorem neg_kron (A B : Matrix (Fin N) (Fin N) ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ A, Matrix.smul_kronecker, neg_one_smul]

/-- `⊗ₖ` distributes over negation on the right. -/
theorem kron_neg (A B : Matrix (Fin N) (Fin N) ℂ) : A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  rw [← neg_one_smul ℂ B, Matrix.kronecker_smul, neg_one_smul]

/-- `⊗ₖ` distributes over subtraction on the left. -/
theorem sub_kron (A₁ A₂ B : Matrix (Fin N) (Fin N) ℂ) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  rw [sub_eq_add_neg, Matrix.add_kronecker, neg_kron, ← sub_eq_add_neg]

/-- `⊗ₖ` distributes over subtraction on the right. -/
theorem kron_sub (A B₁ B₂ : Matrix (Fin N) (Fin N) ℂ) :
    A ⊗ₖ (B₁ - B₂) = A ⊗ₖ B₁ - A ⊗ₖ B₂ := by
  rw [sub_eq_add_neg, Matrix.kronecker_add, kron_neg, ← sub_eq_add_neg]

/-- `⊗ₖ` distributes over a finite sum on the left. -/
theorem sum_kron_left {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin N) (Fin N) ℂ) (B : Matrix (Fin N) (Fin N) ℂ) :
    (∑ i ∈ s, f i) ⊗ₖ B = ∑ i ∈ s, f i ⊗ₖ B := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.add_kronecker, ih]

/-- `⊗ₖ` distributes over a finite sum on the right. -/
theorem kron_sum_right {ι : Type*} (B : Matrix (Fin N) (Fin N) ℂ)
    (s : Finset ι) (f : ι → Matrix (Fin N) (Fin N) ℂ) :
    B ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, B ⊗ₖ f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.kronecker_add, ih]

/-- **Casimir Lie-invariance `[H, C] = 0` (NEW — value-add).** The quadratic Casimir is annihilated
by the doubled (diagonal/coproduct) adjoint action of every basis element: `C ∈ adCommutantGG`,
i.e. `⁅Bⱼ ⊗ₖ 1 + 1 ⊗ₖ Bⱼ, C⁆ = 0`. (This is the correct coproduct statement; the single-sided
`⁅Bⱼ ⊗ₖ 1, C⁆` does not vanish.) [RBS+23] -/
theorem casimir_mem_adCommutantGG (b : DLAHermBasis gens) :
    b.casimir ∈ adCommutantGG b := by
  rw [adCommutantGG, Submodule.mem_iInf]
  intro j
  rw [LinearMap.mem_ker]
  -- ⁅Bⱼ, Bₖ⁆ lies in g, hence equals its own HS expansion ∑ₗ ⟪Bₗ, ⁅Bⱼ,Bₖ⁆⟫ • Bₗ.
  have hmemB : ∀ i : Fin b.dim, b.B i ∈ dynamicalLieAlgebra gens := by
    intro i
    have : b.B i ∈ (dynamicalLieAlgebra gens).toSubmodule := by
      rw [← b.span_eq]; exact Submodule.subset_span (Set.mem_range_self i)
    exact this
  have hbr : ∀ k, ⁅b.B j, b.B k⁆ = ∑ l, hsInner (b.B l) ⁅b.B j, b.B k⁆ • b.B l := by
    intro k
    have hmem : ⁅b.B j, b.B k⁆ ∈ (dynamicalLieAlgebra gens).toSubmodule :=
      LieSubalgebra.lie_mem _ (hmemB j) (hmemB k)
    conv_lhs => rw [← gProj_eq_self_of_mem b hmem]
    rfl
  -- Expand the doubled action of Bⱼ on the Casimir.
  have expand : doubledAd (b.B j) b.casimir
      = ∑ k, (⁅b.B j, b.B k⁆ ⊗ₖ b.B k + b.B k ⊗ₖ ⁅b.B j, b.B k⁆) := by
    simp only [doubledAd, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      DLAHermBasis.casimir, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [add_mul, mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one, Ring.lie_def, sub_kron, kron_sub]
    abel
  rw [expand]
  -- Substitute the expansion and distribute ⊗ₖ over the sums and scalars.
  have step : ∑ k, (⁅b.B j, b.B k⁆ ⊗ₖ b.B k + b.B k ⊗ₖ ⁅b.B j, b.B k⁆)
      = ∑ k, ∑ l, hsInner (b.B l) ⁅b.B j, b.B k⁆ • (b.B l ⊗ₖ b.B k + b.B k ⊗ₖ b.B l) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [hbr k]
    rw [sum_kron_left, kron_sum_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_kronecker, kronecker_smul, smul_add]
  rw [step]
  -- The double sum is antisymmetric under k ↔ l against a symmetric tensor, hence S = -S = 0.
  set S := ∑ k, ∑ l, hsInner (b.B l) ⁅b.B j, b.B k⁆ • (b.B l ⊗ₖ b.B k + b.B k ⊗ₖ b.B l) with hSdef
  have hSneg : S = -S := by
    rw [hSdef]
    nth_rewrite 1 [show
        (∑ k, ∑ l, hsInner (b.B l) ⁅b.B j, b.B k⁆ •
          (b.B l ⊗ₖ b.B k + b.B k ⊗ₖ b.B l))
          = ∑ k, ∑ l, hsInner (b.B k) ⁅b.B j, b.B l⁆ • (b.B k ⊗ₖ b.B l + b.B l ⊗ₖ b.B k)
        from Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsInner_bracket_antisymm b j l k, add_comm (b.B k ⊗ₖ b.B l) (b.B l ⊗ₖ b.B k), neg_smul]
  have h2 : (2 : ℂ) • S = 0 := by
    rw [two_smul]; nth_rewrite 1 [hSneg]; exact neg_add_cancel S
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **The Casimir lies in the variance-relevant invariant subspace `(g⊗g)^g`.** It is both
`g`-invariant (`casimir_mem_adCommutantGG`) and inside the `g ⊗ g` carrier (`casimir_mem_gTensorG`),
hence in their intersection `gTensorGInvariant`. This is the structural inhabitant the
de-circularized variance law's `mem_invariant` hypothesis is discharged against. -/
theorem casimir_mem_gTensorGInvariant (b : DLAHermBasis gens) :
    b.casimir ∈ gTensorGInvariant b := by
  rw [gTensorGInvariant]
  exact Submodule.mem_inf.mpr ⟨casimir_mem_adCommutantGG b, casimir_mem_gTensorG b⟩

end QuantumAlg
