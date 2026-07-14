/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Simulation.GSim
public import QuantumAlg.Primitives.QNN.Designs.ProductClifford
public import QuantumAlg.Primitives.QNN.Algebras.SingleQubitDLA

/-!
# g-sim for the local `su(2)^n` family

This module wires the locality witness from `SingleQubitDLA` to the g-sim
reconstruction theorem. The new data are the product-local Hermitian basis of
dimension `3 * n`, its DLA span proof, and the resulting exact reconstruction
from the `3n` quantum data `Tr[rho B_j]`.

The variance side is witnessed by the genuine product single-qubit-Clifford
doubled twirl. The full product ensemble marginalizes to the distinguished
site, where `QubitTwoDesign.qubitClifford_twirl_basis_zero` supplies the
single-qubit `t = 2` design equality.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Nat}

/-! ## Product-local basis -/

/-- Index `Fin (3 * n)` as `(Pauli component, site)`. -/
def localIdx (j : Fin n) (a : Fin 3) : Fin (3 * n) :=
  finProdFinEquiv (a, j)

/-- The product-local Hermitian basis: the embedded normalized single-site
`X`, `Y`, `Z` operators, indexed over all sites. -/
noncomputable def localB (n : Nat) (i : Fin (3 * n)) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  embB (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).1

@[simp] theorem localB_localIdx (j : Fin n) (a : Fin 3) :
    localB n (localIdx j a) = embB j a := by
  simp [localB, localIdx]

/-- The skew-Hermitian generator set for the product DLA `su(2)^n`. -/
noncomputable def localGens (n : Nat) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  Set.range fun i : Fin (3 * n) => Complex.I • localB n i

/-- The linear span of the product-local Hermitian basis. -/
noncomputable def localSpan (n : Nat) :
    Submodule ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  Submodule.span ℂ (Set.range (localB n))

theorem localB_mem_span (i : Fin (3 * n)) :
    localB n i ∈ localSpan n :=
  Submodule.subset_span ⟨i, rfl⟩

theorem embB_mem_localSpan (j : Fin n) (a : Fin 3) :
    embB j a ∈ localSpan n := by
  rw [← localB_localIdx j a]
  exact localB_mem_span (localIdx j a)

theorem emb_span_le_localSpan (j : Fin n) :
    Submodule.span ℂ (Set.range (embB j)) ≤ localSpan n := by
  rw [Submodule.span_le]
  intro X hX
  obtain ⟨a, rfl⟩ := hX
  exact embB_mem_localSpan j a

theorem embB_lie_mem_localSpan_same (j : Fin n) (a b : Fin 3) :
    ⁅embB j a, embB j b⁆ ∈ localSpan n := by
  have hx : embB j a ∈ Submodule.span ℂ (embSet j) := by
    rw [← emb_range_span j]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hy : embB j b ∈ Submodule.span ℂ (embSet j) := by
    rw [← emb_range_span j]
    exact Submodule.subset_span ⟨b, rfl⟩
  have h := emb_lie_mem_span j hx hy
  rw [← emb_range_span j] at h
  exact emb_span_le_localSpan j h

theorem localB_lie_mem_span (i j : Fin (3 * n)) :
    ⁅localB n i, localB n j⁆ ∈ localSpan n := by
  by_cases hsite : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2
  · rw [localB, localB]
    rw [hsite]
    exact embB_lie_mem_localSpan_same _ _ _
  · rw [localB, localB, embB_cross_lie_zero hsite]
    exact zero_mem _

/-- The product-local span is closed under the matrix commutator. -/
theorem localSpan_lie_mem {x y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (hx : x ∈ localSpan n) (hy : y ∈ localSpan n) :
    ⁅x, y⁆ ∈ localSpan n := by
  change x ∈ Submodule.span ℂ (Set.range (localB n)) at hx
  change y ∈ Submodule.span ℂ (Set.range (localB n)) at hy
  induction hx using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨i, rfl⟩ := hX
      induction hy using Submodule.span_induction with
      | mem Y hY =>
          obtain ⟨j, rfl⟩ := hY
          exact localB_lie_mem_span i j
      | zero =>
          rw [lie_zero]
          exact zero_mem _
      | add y z _ _ hy hz =>
          rw [lie_add]
          exact add_mem hy hz
      | smul c y _ hy =>
          rw [lie_smul]
          exact Submodule.smul_mem _ _ hy
  | zero =>
      rw [zero_lie]
      exact zero_mem _
  | add x y _ _ hx hy =>
      rw [add_lie]
      exact add_mem hx hy
  | smul c x _ hx =>
      rw [smul_lie]
      exact Submodule.smul_mem _ _ hx

/-- `localSpan` as a Lie subalgebra. -/
noncomputable def localLie (n : Nat) :
    LieSubalgebra ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) where
  toSubmodule := localSpan n
  lie_mem' := fun hx hy => localSpan_lie_mem hx hy

theorem localGens_subset_localLie (n : Nat) :
    localGens n ⊆ (localLie n : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
  intro A hA
  obtain ⟨i, rfl⟩ := hA
  exact Submodule.smul_mem _ _ (localB_mem_span i)

/-- The product-local DLA is exactly the span of the `3n` local Pauli basis. -/
theorem local_dla_toSubmodule (n : Nat) :
    (dynamicalLieAlgebra (localGens n)).toSubmodule = localSpan n := by
  apply le_antisymm
  · intro x hx
    exact dynamicalLieAlgebra_minimal (localGens n) (localGens_subset_localLie n) hx
  · change Submodule.span ℂ (Set.range (localB n)) ≤
      (dynamicalLieAlgebra (localGens n)).toSubmodule
    rw [Submodule.span_le]
    intro X hX
    obtain ⟨i, rfl⟩ := hX
    have hgen : Complex.I • localB n i ∈ dynamicalLieAlgebra (localGens n) :=
      generators_subset_dynamicalLieAlgebra (localGens n) ⟨i, rfl⟩
    have hmem := Submodule.smul_mem (dynamicalLieAlgebra (localGens n)).toSubmodule
      (-Complex.I) hgen
    have hkey : (-Complex.I) • (Complex.I • localB n i) = localB n i := by
      rw [smul_smul]
      simp [Complex.I_mul_I]
    rwa [hkey] at hmem

theorem localB_herm (i : Fin (3 * n)) : (localB n i)ᴴ = localB n i := by
  rw [localB, embB_isHermitian]

theorem localB_ortho (i j : Fin (3 * n)) :
    hsInner (localB n i) (localB n j) = if i = j then 1 else 0 := by
  by_cases hsite : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2
  · rw [localB, localB]
    rw [hsite]
    rw [embB_ortho]
    by_cases hcomp : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
    · have hij : i = j := by
        exact finProdFinEquiv.symm.injective (Prod.ext hcomp hsite)
      rw [if_pos hcomp, if_pos hij]
    · have hij : i ≠ j := by
        intro hij
        exact hcomp (congrArg (fun k => (finProdFinEquiv.symm k).1) hij)
      rw [if_neg hcomp, if_neg hij]
  · rw [localB, localB]
    have hzero :
        hsInner (embB (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm i).1)
          (embB (finProdFinEquiv.symm j).2 (finProdFinEquiv.symm j).1) = 0 := by
      simpa [su2EmbHermBasis_B] using
        (emb_cross_ortho hsite (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1)
    rw [hzero]
    have hij : i ≠ j := by
      intro hij
      exact hsite (congrArg (fun k => (finProdFinEquiv.symm k).2) hij)
    rw [if_neg hij]

/-- Hermitian orthonormal basis of the product-local DLA `su(2)^n`, with
dimension `3 * n`. -/
noncomputable def localHermBasis (n : Nat) : DLAHermBasis (localGens n) where
  dim := 3 * n
  B := localB n
  herm := localB_herm
  ortho := localB_ortho
  span_eq := (local_dla_toSubmodule n).symm

@[simp] theorem localHermBasis_dim (n : Nat) : (localHermBasis n).dim = 3 * n := rfl

@[simp] theorem localHermBasis_B (n : Nat) : (localHermBasis n).B = localB n := rfl

theorem localObs_mem_product_dla (hn : 0 < n) :
    localObs hn ∈ (dynamicalLieAlgebra (localGens n)).toSubmodule := by
  have hB := (localHermBasis n).basis_mem_dla (localIdx (⟨0, hn⟩ : Fin n) 0)
  rw [localHermBasis_B, localB_localIdx] at hB
  have hO : localObs hn = (rtNinv n)⁻¹ • embB (⟨0, hn⟩ : Fin n) 0 := by
    rw [embB_zero, localObs, smul_smul, inv_mul_cancel₀ (rtNinv_ne_zero n), one_smul]
  rw [hO]
  exact Submodule.smul_mem _ _ hB

/-! ## Family-level reconstruction and dichotomy witness -/

/-- For the product-local DLA `su(2)^n`, every gate list drawn from that DLA has
its local-observable loss exactly reconstructed from the `3n` quantum data
`Tr[localState * B_j]`. -/
theorem localObs_loss_reconstruction_from_3n (hn : 0 < n)
    {Gs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)}
    (hGs : ∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (localGens n)).toSubmodule) :
    ((Gs.map NormedSpace.exp).prod * localState
        * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * localObs hn).trace
      = ∑ j, hsInner ((localHermBasis n).B j) (gsimEvolved Gs (localObs hn))
          * (localState * (localHermBasis n).B j).trace :=
  gsim_loss_reconstruction_ansatz (localHermBasis n) hGs localState
    (localObs_mem_product_dla hn)

/-- The reductive sum for the unscaled local observable collapses to the distinguished-site
closed form `1/3`. -/
theorem localObs_productClifford_reductive_sum_closed_eq (hn : 0 < n) :
    (∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ))
      = 1 / 3 := by
  have hterm : ∀ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ)
      = if j = ⟨0, hn⟩ then 1 / 3 else 0 := by
    intro j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [gPurity_localState, gPurity_localObs_diag, if_pos rfl, su2EmbHermBasis_dim,
        inv_mul_cancel₀ (pow_ne_zero n (two_ne_zero))]
      norm_num
    · rw [gPurity_localObs_offdiag hn j hj, mul_zero, zero_div, if_neg hj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]

/-- The genuine product-Clifford reductive witness for the local `su(2)^n` family. Its
`secondMoment` is the full product single-qubit-Clifford doubled twirl of `localObs ⊗ localObs`;
the proved closed-form twirl equality concentrates it on the distinguished-site ideal block, so
the per-ideal diagonal membership (`diagBlock_mem_invariant`) and the cross-ideal
invariant-block exclusion (`cross_block_exclusion`) are both discharged constructively. -/
noncomputable def rLocalProductClifford (hn : 0 < n) :
    RagoneReductive (localState (n := n)) (localObs hn) where
  numComp := n
  gens := embGens
  basis := su2EmbHermBasis
  cross_ortho := fun _ _ hij a b => emb_cross_ortho hij a b
  variance := (∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
    * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ)).re
  secondMoment := twirl2 (productQubitClifford (n := n)) (localObs hn ⊗ₖ localObs hn)
  diagBlock := fun j => if j = ⟨0, hn⟩ then
    ((2 ^ n : ℂ) / 3) • (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).casimir else 0
  var_eq := by
    have hvar :
        (((∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
          * (su2EmbHermBasis j).gPurity (localObs hn) /
            ((su2EmbHermBasis j).dim : ℂ)).re : ℝ) : ℂ) = 1 / 3 := by
      rw [localObs_productClifford_reductive_sum_closed_eq hn]
      norm_num
    have htwirl : hsInner (localState (n := n) ⊗ₖ localState (n := n))
        (twirl2 (productQubitClifford (n := n)) (localObs hn ⊗ₖ localObs hn)) = 1 / 3 := by
      let j0 : Fin n := ⟨0, hn⟩
      have hρρ : (localState (n := n) ⊗ₖ localState (n := n))ᴴ =
          localState (n := n) ⊗ₖ localState (n := n) := by
        rw [conjTranspose_kronecker, localState_herm]
      rw [productQubitClifford_twirl_localObs hn, hsInner_smul_right,
        hsInner_comm_of_isHermitian hρρ (su2EmbHermBasis j0).casimir_isHermitian,
        (su2EmbHermBasis j0).casimir_hsInner_kron localState_herm, gPurity_localState]
      have hpow : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hpow]
    rw [hvar, htwirl]
  diagBlock_mem_invariant := by
    intro j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [if_pos rfl]
      exact Submodule.smul_mem _ _ (casimir_mem_gTensorGInvariant (su2EmbHermBasis _))
    · rw [if_neg hj]
      exact Submodule.zero_mem _
  cross_block_exclusion := by
    rw [productQubitClifford_twirl_localObs hn, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  invariant_eq_spanC := su2EmbHermBasis_schur
  proj_orth := by
    let j0 : Fin n := ⟨0, hn⟩
    intro j
    rw [productQubitClifford_twirl_localObs hn, hsInner_smul_right,
      (su2EmbHermBasis j).casimir_hsInner_kron (localObs_herm hn)]
    by_cases hj : j = j0
    · subst hj
      rw [gPurity_localObs_diag hn, (su2EmbHermBasis j0).casimir_hsInner_self,
        su2EmbHermBasis_dim]
      ring
    · rw [gPurity_localObs_offdiag hn j hj,
        casimir_cross_aux su2EmbHermBasis (fun _ _ hij a b => emb_cross_ortho hij a b) j j0,
        if_neg hj, mul_zero]

/-- Product-Clifford variance routed through the reductive g-sim capstone. -/
theorem localObs_productClifford_reductive_sum_eq (hn : 0 < n) :
    ((rLocalProductClifford hn).variance : ℂ) =
      ∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity (localObs hn) / ((su2EmbHermBasis j).dim : ℂ) :=
  (gsim_variance_and_reconstruction_reductive (localHermBasis n)
    (rLocalProductClifford hn) localState_herm (localObs_herm hn)
    su2EmbHermBasis_dim_pos (localObs_mem_product_dla hn)).1

/-- The product-local `su(2)^n` variance witness is the genuine product-Clifford twirl witness,
and its compatibility closed form is exactly `1/3` for every nonempty register. -/
theorem localObs_productClifford_totalVariance_eq (hn : 0 < n) :
    (rLocalProductClifford hn).variance = 1 / 3 := by
  have key : ((rLocalProductClifford hn).variance : ℂ) = 1 / 3 := by
    rw [localObs_productClifford_reductive_sum_eq hn,
      localObs_productClifford_reductive_sum_closed_eq hn]
  have hcast : ((rLocalProductClifford hn).variance : ℂ) = ((1 / 3 : ℝ) : ℂ) := by
    rw [key]; push_cast; ring
  exact_mod_cast hcast

/-- The `secondMoment` field of the local product-Clifford witness is the genuine product twirl
closed form. This endpoint keeps the H1 equality visible to kernel-clean axiom checking. -/
theorem localObs_productClifford_secondMoment_eq (hn : 0 < n) :
    (rLocalProductClifford hn).secondMoment =
      ((2 ^ n : ℂ) / 3) • (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).casimir :=
  productQubitClifford_twirl_localObs hn

/-- Family-level dichotomy for `su(2)^n`: the genuine product-Clifford variance
witness is exactly `1/3` for every nonempty register, and the loss for every
product-local DLA gate list reconstructs from `3n` quantum data. -/
theorem localObs_family_dichotomy (hn : 0 < n) :
    (rLocalProductClifford hn).variance = 1 / 3
    ∧ ∀ (Gs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (localGens n)).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * localState
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * localObs hn).trace
          = ∑ j, hsInner ((localHermBasis n).B j) (gsimEvolved Gs (localObs hn))
              * (localState * (localHermBasis n).B j).trace :=
  ⟨localObs_productClifford_totalVariance_eq hn,
    (gsim_variance_and_reconstruction_reductive (localHermBasis n)
      (rLocalProductClifford hn) localState_herm (localObs_herm hn)
      su2EmbHermBasis_dim_pos (localObs_mem_product_dla hn)).2⟩

/-- Scaling both observable inputs by `1/3` scales the genuine product-Clifford doubled
twirl by `1/9`, so the distinguished-site Casimir coefficient is `2^n / 27`.
This is the closed-form twirl equality used for the scaled distinguished-ideal
purity product; it does not assert bounds on the individual per-ideal purities. -/
theorem localObs_productClifford_scaled_secondMoment_eq (hn : 0 < n) :
    twirl2 (productQubitClifford (n := n))
        (((1 / 3 : ℂ) • localObs hn) ⊗ₖ ((1 / 3 : ℂ) • localObs hn)) =
      ((2 ^ n : ℂ) / 27) • (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).casimir := by
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    twirl2_smul, productQubitClifford_twirl_localObs hn, smul_smul]
  congr 1
  ring

/-- The reductive sum for the scaled local observable collapses to the distinguished-site
closed form `1/27`. -/
theorem localObs_productClifford_scaled_reductive_sum_closed_eq (hn : 0 < n) :
    (∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity ((1 / 3 : ℂ) • localObs hn)
          / ((su2EmbHermBasis j).dim : ℂ)) = 1 / 27 := by
  have hterm : ∀ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity ((1 / 3 : ℂ) • localObs hn)
          / ((su2EmbHermBasis j).dim : ℂ)
      = if j = ⟨0, hn⟩ then 1 / 27 else 0 := by
    intro j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [gPurity_localState, gPurity_smul, gPurity_localObs_diag, if_pos rfl,
        su2EmbHermBasis_dim]
      have hpow : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)
      field_simp [hpow]
      norm_num [Complex.normSq]
    · rw [gPurity_smul, gPurity_localObs_offdiag hn j hj, mul_zero, mul_zero,
        zero_div, if_neg hj]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]

/-- The genuine product-Clifford reductive witness for the scaled local observable.
The distinguished ideal has purity product `1/9`, yielding variance `1/27`;
individual observable purities are not claimed to lie between zero and one. As in the
unscaled witness, the closed-form twirl equality concentrates the second moment on the
distinguished-site ideal block, discharging both the per-ideal diagonal membership and the
cross-ideal invariant-block exclusion constructively. -/
noncomputable def rLocalProductCliffordScaled (hn : 0 < n) :
    RagoneReductive (localState (n := n)) ((1 / 3 : ℂ) • localObs hn) where
  numComp := n
  gens := embGens
  basis := su2EmbHermBasis
  cross_ortho := fun _ _ hij a b => emb_cross_ortho hij a b
  variance := (∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
    * (su2EmbHermBasis j).gPurity ((1 / 3 : ℂ) • localObs hn)
      / ((su2EmbHermBasis j).dim : ℂ)).re
  secondMoment := twirl2 (productQubitClifford (n := n))
    (((1 / 3 : ℂ) • localObs hn) ⊗ₖ ((1 / 3 : ℂ) • localObs hn))
  diagBlock := fun j => if j = ⟨0, hn⟩ then
    ((2 ^ n : ℂ) / 27) • (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).casimir else 0
  var_eq := by
    have hvar :
        (((∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
          * (su2EmbHermBasis j).gPurity ((1 / 3 : ℂ) • localObs hn)
            / ((su2EmbHermBasis j).dim : ℂ)).re : ℝ) : ℂ) = 1 / 27 := by
      rw [localObs_productClifford_scaled_reductive_sum_closed_eq hn]
      norm_num
    have htwirl : hsInner (localState (n := n) ⊗ₖ localState (n := n))
        (twirl2 (productQubitClifford (n := n))
          (((1 / 3 : ℂ) • localObs hn) ⊗ₖ ((1 / 3 : ℂ) • localObs hn))) = 1 / 27 := by
      let j0 : Fin n := ⟨0, hn⟩
      have hρρ : (localState (n := n) ⊗ₖ localState (n := n))ᴴ =
          localState (n := n) ⊗ₖ localState (n := n) := by
        rw [conjTranspose_kronecker, localState_herm]
      rw [localObs_productClifford_scaled_secondMoment_eq hn, hsInner_smul_right,
        hsInner_comm_of_isHermitian hρρ (su2EmbHermBasis j0).casimir_isHermitian,
        (su2EmbHermBasis j0).casimir_hsInner_kron localState_herm, gPurity_localState]
      have hpow : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num)
      field_simp [hpow]
    rw [hvar, htwirl]
  diagBlock_mem_invariant := by
    intro j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      rw [if_pos rfl]
      exact Submodule.smul_mem _ _ (casimir_mem_gTensorGInvariant (su2EmbHermBasis _))
    · rw [if_neg hj]
      exact Submodule.zero_mem _
  cross_block_exclusion := by
    rw [localObs_productClifford_scaled_secondMoment_eq hn, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _)]
  invariant_eq_spanC := su2EmbHermBasis_schur
  proj_orth := by
    let j0 : Fin n := ⟨0, hn⟩
    intro j
    have hOscaled : (((1 / 3 : ℂ) • localObs hn)ᴴ =
        (1 / 3 : ℂ) • localObs hn) := by
      rw [Matrix.conjTranspose_smul, localObs_herm hn]
      norm_num
    rw [localObs_productClifford_scaled_secondMoment_eq hn, hsInner_smul_right,
      (su2EmbHermBasis j).casimir_hsInner_kron hOscaled]
    by_cases hj : j = j0
    · subst hj
      rw [gPurity_smul, gPurity_localObs_diag hn,
        (su2EmbHermBasis j0).casimir_hsInner_self, su2EmbHermBasis_dim]
      norm_num [Complex.normSq]
      ring
    · rw [gPurity_smul, gPurity_localObs_offdiag hn j hj,
        casimir_cross_aux su2EmbHermBasis (fun _ _ hij a b => emb_cross_ortho hij a b) j j0,
        if_neg hj, mul_zero]
      simp

/-- Scaled product-Clifford variance routed through the reductive g-sim capstone. -/
theorem localObs_productClifford_scaled_reductive_sum_eq (hn : 0 < n) :
    ((rLocalProductCliffordScaled hn).variance : ℂ) =
      ∑ j : Fin n, (su2EmbHermBasis j).gPurity (localState (n := n))
        * (su2EmbHermBasis j).gPurity ((1 / 3 : ℂ) • localObs hn)
          / ((su2EmbHermBasis j).dim : ℂ) := by
  have hOscaled : (((1 / 3 : ℂ) • localObs hn)ᴴ =
      (1 / 3 : ℂ) • localObs hn) := by
    rw [Matrix.conjTranspose_smul, localObs_herm hn]
    norm_num
  exact (gsim_variance_and_reconstruction_reductive (localHermBasis n)
    (rLocalProductCliffordScaled hn) localState_herm hOscaled
    su2EmbHermBasis_dim_pos (Submodule.smul_mem _ _ (localObs_mem_product_dla hn))).1

/-- The scaled product-local witness has compatibility closed form `1/27`,
derived from the reductive sum rather than by reducing the witness field. -/
theorem localObs_productClifford_scaled_totalVariance_eq (hn : 0 < n) :
    (rLocalProductCliffordScaled hn).variance = 1 / 27 := by
  have key : ((rLocalProductCliffordScaled hn).variance : ℂ) = 1 / 27 := by
    rw [localObs_productClifford_scaled_reductive_sum_eq hn,
      localObs_productClifford_scaled_reductive_sum_closed_eq hn]
  have hcast : ((rLocalProductCliffordScaled hn).variance : ℂ) = ((1 / 27 : ℝ) : ℂ) := by
    rw [key]; push_cast; ring
  exact_mod_cast hcast

/-- Family-level dichotomy for the scaled local observable: the genuine product-Clifford
variance witness is exactly `1/27` for every nonempty register, and the same
`3n` quantum data reconstructs every scaled-observable loss. The variance uses
only the distinguished-ideal purity product `1/9`, not individual per-ideal
purity bounds. -/
theorem localObs_family_dichotomy_scaled (hn : 0 < n) :
    (rLocalProductCliffordScaled hn).variance = 1 / 27
    ∧ ∀ (Gs : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)),
        (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (localGens n)).toSubmodule) →
        ((Gs.map NormedSpace.exp).prod * localState
            * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod
            * ((1 / 3 : ℂ) • localObs hn)).trace
          = ∑ j, hsInner ((localHermBasis n).B j)
              (gsimEvolved Gs ((1 / 3 : ℂ) • localObs hn))
              * (localState * (localHermBasis n).B j).trace := by
  have hOscaled : (((1 / 3 : ℂ) • localObs hn)ᴴ =
      (1 / 3 : ℂ) • localObs hn) := by
    rw [Matrix.conjTranspose_smul, localObs_herm hn]
    norm_num
  exact ⟨localObs_productClifford_scaled_totalVariance_eq hn,
    (gsim_variance_and_reconstruction_reductive (localHermBasis n)
      (rLocalProductCliffordScaled hn) localState_herm hOscaled
      su2EmbHermBasis_dim_pos (Submodule.smul_mem _ _ (localObs_mem_product_dla hn))).2⟩

end QuantumAlg
