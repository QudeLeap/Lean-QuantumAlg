/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Designs.QubitTwoDesign
public import QuantumAlg.Primitives.QNN.Algebras.SingleQubitDLA

/-!
# Product single-qubit Clifford twirl

This module packages the `n`-fold product of the strict single-qubit Clifford
lift and the doubled-twirl endpoint used by the local `su(2)^n` g-sim witness.
It is deliberately independent from the g-sim simulation capstone: consumers
should depend on this module when they need the product-Clifford design calculation.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Nat}

/-! ## The product single-qubit Clifford twirl -/

/-- The tensor product of single-qubit gates, written over the register index
`Fin n → Fin 2`. -/
noncomputable def productGateStr (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ j, U j (x j) (y j)

/-- The same tensor product, reindexed to the library convention `Fin (2 ^ n)`. -/
noncomputable def productGate (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (productGateStr U).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

/-- The full `n`-fold product of the strict `48`-element single-qubit Clifford lift. -/
noncomputable def productQubitClifford
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  productGate fun j => QubitTwoDesign.qubitClifford (g j)

/-- Lift a one-qubit operator to site `j`, over the register index `Fin n → Fin 2`. -/
noncomputable def singleSiteGateStr (j : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  productGateStr fun k => if k = j then M else 1

/-- Lift a one-qubit operator to site `j`, reindexed to `Fin (2 ^ n)`. -/
noncomputable def singleSiteGate (j : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (singleSiteGateStr j M).submatrix finFunctionFinEquiv.symm finFunctionFinEquiv.symm

theorem productGateStr_mul (U V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    productGateStr U * productGateStr V = productGateStr (fun j => U j * V j) := by
  ext x z
  have hfac : ∀ j, (U j * V j) (x j) (z j)
      = ∑ yj : Fin 2, U j (x j) yj * V j yj (z j) := fun j => Matrix.mul_apply
  rw [Matrix.mul_apply]
  simp only [productGateStr, Matrix.of_apply]
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 2)))
      (fun (j : Fin n) (yj : Fin 2) => U j (x j) yj * V j yj (z j)),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem productGate_mul (U V : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    productGate U * productGate V = productGate (fun j => U j * V j) := by
  rw [productGate, productGate, productGate, Matrix.submatrix_mul_equiv, productGateStr_mul]

theorem productGateStr_conjTranspose (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (productGateStr U)ᴴ = productGateStr fun j => (U j)ᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, productGateStr, Matrix.of_apply]
  rw [← starRingEnd_apply, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rfl

theorem productGate_conjTranspose (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (productGate U)ᴴ = productGate fun j => (U j)ᴴ := by
  rw [productGate, productGate, Matrix.conjTranspose_submatrix, productGateStr_conjTranspose]

theorem productGateStr_one :
    productGateStr (n := n) (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [productGateStr, Matrix.one_apply]
  · have hne : ∃ j, x j ≠ y j := Function.ne_iff.mp hxy
    obtain ⟨j, hj⟩ := hne
    rw [productGateStr, Matrix.of_apply, Matrix.one_apply, if_neg hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem productGate_one :
    productGate (n := n) (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 := by
  rw [productGate, productGateStr_one, Matrix.submatrix_one_equiv]

theorem productQubitClifford_mul
    (a b : Fin n → QubitTwoDesign.BinaryOctahedral) :
    productQubitClifford (a * b) = productQubitClifford a * productQubitClifford b := by
  rw [productQubitClifford, productQubitClifford, productQubitClifford, productGate_mul]
  congr 1
  funext j
  exact QubitTwoDesign.qubitClifford_mul (a j) (b j)

theorem productQubitClifford_unitary
    (g : Fin n → QubitTwoDesign.BinaryOctahedral) :
    (productQubitClifford g)ᴴ * productQubitClifford g = 1 := by
  rw [productQubitClifford, productGate_conjTranspose, productGate_mul]
  have hU : (fun j : Fin n => (QubitTwoDesign.qubitClifford (g j))ᴴ *
      QubitTwoDesign.qubitClifford (g j))
      = fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    funext j
    exact QubitTwoDesign.qubitClifford_unitary (g j)
  rw [hU, productGate_one]

theorem singleSiteGate_pauli (j : Fin n) (a : Fin 4) :
    singleSiteGate j (pauli1 a) = pauliMat (siteP j a) := by
  rw [singleSiteGate, pauliMat]
  ext x y
  simp only [Matrix.submatrix_apply, singleSiteGateStr, productGateStr, pauliStr, Matrix.of_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hkj : k = j
  · rw [if_pos hkj, hkj, siteP_same]
  · rw [if_neg hkj, siteP_ne a hkj, pauli1_zero]

/-- Split product-function data into the distinguished site and all remaining sites. -/
noncomputable def piAtEquiv (j : Fin n) (α : Type*) :
    (Fin n → α) ≃ α × ({k : Fin n // k ≠ j} → α) where
  toFun f := (f j, fun k => f k.1)
  invFun p k := if h : k = j then p.1 else p.2 ⟨k, h⟩
  left_inv f := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  right_inv p := by
    ext k
    · simp
    · simp [k.2]

theorem sum_pi_eval_eq_card_smul {α M : Type*} [Fintype α] [AddCommMonoid M]
    [Module ℂ M] (j : Fin n) (F : α → M) :
    ∑ g : Fin n → α, F (g j) =
      (Fintype.card ({k : Fin n // k ≠ j} → α) : ℂ) • ∑ a : α, F a := by
  classical
  calc
    ∑ g : Fin n → α, F (g j)
        = ∑ p : α × ({k : Fin n // k ≠ j} → α), F p.1 := by
          simpa [piAtEquiv] using
            (Equiv.sum_comp (piAtEquiv (n := n) j α) (fun p => F p.1))
    _ = ∑ a : α, ∑ _ : ({k : Fin n // k ≠ j} → α), F a := by
          rw [Fintype.sum_prod_type]
    _ = (Fintype.card ({k : Fin n // k ≠ j} → α) : ℂ) • ∑ a : α, F a := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

theorem card_pi_eq_card_rest_mul {α : Type*} [Fintype α] (j : Fin n) :
    (Fintype.card (Fin n → α) : ℂ) =
      (Fintype.card ({k : Fin n // k ≠ j} → α) : ℂ) * (Fintype.card α : ℂ) := by
  have h := Fintype.card_congr (piAtEquiv (n := n) j α)
  rw [Fintype.card_prod] at h
  rw [h, Nat.cast_mul]
  ring

theorem singleSiteGate_apply (j : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (p q : Fin (2 ^ n)) :
    singleSiteGate j M p q =
      M (finFunctionFinEquiv.symm p j) (finFunctionFinEquiv.symm q j)
        * ∏ k ∈ Finset.univ.erase j,
            (1 : Matrix (Fin 2) (Fin 2) ℂ)
              (finFunctionFinEquiv.symm p k) (finFunctionFinEquiv.symm q k) := by
  rw [singleSiteGate, singleSiteGateStr, productGateStr, Matrix.submatrix_apply, Matrix.of_apply,
    ← Finset.mul_prod_erase Finset.univ
      (fun k => (if k = j then M else 1)
        (finFunctionFinEquiv.symm p k) (finFunctionFinEquiv.symm q k))
      (Finset.mem_univ j)]
  congr 1
  · rw [if_pos rfl]
  · refine Finset.prod_congr rfl fun k hk => ?_
    rw [if_neg (Finset.ne_of_mem_erase hk)]

theorem singleSiteGate_smul (j : Fin n) (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    singleSiteGate j (c • M) = c • singleSiteGate j M := by
  ext p q
  rw [singleSiteGate_apply]
  simp [Matrix.smul_apply, singleSiteGate_apply, mul_assoc]

theorem singleSiteGate_su2B (j : Fin n) (i : Fin 3) :
    singleSiteGate j (su2HermBasis.B i) =
      (rt2inv * (rtNinv n)⁻¹) • (su2EmbHermBasis j).B i := by
  have hX : singleSiteGate j pauliX = pauliMat (siteP j 1) := by
    simpa [pauli1] using singleSiteGate_pauli (n := n) j 1
  have hY : singleSiteGate j pauliY = pauliMat (siteP j 2) := by
    simpa [pauli1] using singleSiteGate_pauli (n := n) j 2
  have hZ : singleSiteGate j pauliZ = pauliMat (siteP j 3) := by
    simpa [pauli1] using singleSiteGate_pauli (n := n) j 3
  have hcoef : rt2inv * (rtNinv n)⁻¹ * rtNinv n = rt2inv := by
    rw [mul_assoc, inv_mul_cancel₀ (rtNinv_ne_zero n), mul_one]
  rw [su2HermBasis_B, su2EmbHermBasis_B]
  fin_cases i <;>
    simp [su2B, embB, singleSiteGate_smul, hX, hY, hZ, smul_smul, hcoef]

/-- Lift a doubled one-qubit operator to the doubled register on site `j`. -/
noncomputable def singleSiteDoubledGate (j : Fin n)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ n) × Fin (2 ^ n)) ℂ :=
  Matrix.of fun p q =>
    X (finFunctionFinEquiv.symm p.1 j, finFunctionFinEquiv.symm p.2 j)
      (finFunctionFinEquiv.symm q.1 j, finFunctionFinEquiv.symm q.2 j)
      * (∏ k ∈ Finset.univ.erase j,
          (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (finFunctionFinEquiv.symm p.1 k) (finFunctionFinEquiv.symm q.1 k))
      * (∏ k ∈ Finset.univ.erase j,
          (1 : Matrix (Fin 2) (Fin 2) ℂ)
            (finFunctionFinEquiv.symm p.2 k) (finFunctionFinEquiv.symm q.2 k))

theorem singleSiteDoubledGate_smul (j : Fin n) (c : ℂ)
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    singleSiteDoubledGate j (c • X) = c • singleSiteDoubledGate j X := by
  ext p q
  simp [singleSiteDoubledGate, Matrix.smul_apply, mul_assoc]

theorem singleSiteDoubledGate_sum {α : Type*} (j : Fin n) (F : α → Matrix (Fin 2 × Fin 2)
    (Fin 2 × Fin 2) ℂ) (s : Finset α) :
    singleSiteDoubledGate j (∑ a ∈ s, F a) = ∑ a ∈ s, singleSiteDoubledGate j (F a) := by
  ext p q
  simp only [singleSiteDoubledGate, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.sum_mul, Finset.sum_mul]

theorem singleSiteDoubledGate_kronecker (j : Fin n)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    singleSiteGate j A ⊗ₖ singleSiteGate j B =
      singleSiteDoubledGate j (A ⊗ₖ B) := by
  ext p q
  rw [Matrix.kroneckerMap_apply, singleSiteGate_apply, singleSiteGate_apply]
  simp only [singleSiteDoubledGate, Matrix.of_apply, Matrix.kroneckerMap_apply]
  ring

theorem productGate_conj_singleSite (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hunit : ∀ j, (U j)ᴴ * U j = 1) (j : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    productGate U * singleSiteGate j M * (productGate U)ᴴ =
      singleSiteGate j (U j * M * (U j)ᴴ) := by
  change productGate U * productGate (fun k => if k = j then M else 1) * (productGate U)ᴴ =
    productGate (fun k => if k = j then U j * M * (U j)ᴴ else 1)
  rw [productGate_conjTranspose, productGate_mul, productGate_mul]
  congr 1
  funext k
  by_cases hkj : k = j
  · subst hkj
    simp
  · rw [if_neg hkj, if_neg hkj]
    simp [mul_eq_one_comm.mp (hunit k)]

theorem doubledConj_product_singleSite
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hunit : ∀ j, (U j)ᴴ * U j = 1)
    (j : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    doubledConj (productGate U) (singleSiteGate j M ⊗ₖ singleSiteGate j M) =
      singleSiteDoubledGate j (doubledConj (U j) (M ⊗ₖ M)) := by
  rw [doubledConj, doubledConj, Matrix.conjTranspose_kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rw [productGate_conj_singleSite U hunit j M, singleSiteDoubledGate_kronecker]
  congr 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

theorem productQubitClifford_twirl_singleSite (j : Fin n)
    (M : Matrix (Fin 2) (Fin 2) ℂ) :
    twirl2 (productQubitClifford (n := n)) (singleSiteGate j M ⊗ₖ singleSiteGate j M) =
      singleSiteDoubledGate j (twirl2 QubitTwoDesign.qubitClifford (M ⊗ₖ M)) := by
  let F : QubitTwoDesign.BinaryOctahedral →
      Matrix (Fin (2 ^ n) × Fin (2 ^ n)) (Fin (2 ^ n) × Fin (2 ^ n)) ℂ :=
    fun h => singleSiteDoubledGate j
      (doubledConj (QubitTwoDesign.qubitClifford h) (M ⊗ₖ M))
  have hterm : ∀ g : Fin n → QubitTwoDesign.BinaryOctahedral,
      doubledConj (productQubitClifford g) (singleSiteGate j M ⊗ₖ singleSiteGate j M) =
        F (g j) := by
    intro g
    change doubledConj (productGate fun k => QubitTwoDesign.qubitClifford (g k))
        (singleSiteGate j M ⊗ₖ singleSiteGate j M) =
      singleSiteDoubledGate j
        (doubledConj (QubitTwoDesign.qubitClifford (g j)) (M ⊗ₖ M))
    exact doubledConj_product_singleSite
      (fun k => QubitTwoDesign.qubitClifford (g k))
      (fun k => QubitTwoDesign.qubitClifford_unitary (g k)) j M
  have hsumlift :
      singleSiteDoubledGate j
          (∑ h : QubitTwoDesign.BinaryOctahedral,
            doubledConj (QubitTwoDesign.qubitClifford h) (M ⊗ₖ M))
        = ∑ h : QubitTwoDesign.BinaryOctahedral, F h := by
    change singleSiteDoubledGate j
        (∑ h ∈ Finset.univ, doubledConj (QubitTwoDesign.qubitClifford h) (M ⊗ₖ M))
      = ∑ h ∈ Finset.univ, F h
    rw [singleSiteDoubledGate_sum]
  rw [twirl2_eq_sum_doubledConj, twirl2_eq_sum_doubledConj]
  rw [Finset.sum_congr rfl (fun g _ => hterm g),
    sum_pi_eval_eq_card_smul j F, singleSiteDoubledGate_smul, hsumlift, smul_smul]
  congr 1
  have hcard := card_pi_eq_card_rest_mul (n := n)
    (α := QubitTwoDesign.BinaryOctahedral) j
  have hrest : (Fintype.card ({k : Fin n // k ≠ j} →
      QubitTwoDesign.BinaryOctahedral) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsingle : (Fintype.card QubitTwoDesign.BinaryOctahedral : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hcard]
  field_simp [hrest, hsingle]

theorem qubitClifford_twirl_pauliX :
    twirl2 QubitTwoDesign.qubitClifford (pauliX ⊗ₖ pauliX) =
      (2 / 3 : ℂ) • su2HermBasis.casimir := by
  have hX : pauliX = rt2inv⁻¹ • su2HermBasis.B su2i0 := by
    change pauliX = rt2inv⁻¹ • (rt2inv • pauliX)
    rw [smul_smul, inv_mul_cancel₀ rt2inv_ne_zero, one_smul]
  rw [hX, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    twirl2_smul, QubitTwoDesign.qubitClifford_twirl_basis_zero, smul_smul]
  congr 1
  rw [← _root_.mul_inv_rev, rt2inv_mul_self]
  norm_num

theorem rtNinv_inv_mul_self (n : Nat) :
    (rtNinv n)⁻¹ * (rtNinv n)⁻¹ = (2 ^ n : ℂ) := by
  have h := rtNinv_mul_self n
  have hnz := rtNinv_ne_zero n
  have hpow : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hnz, hpow] at h ⊢
  exact h.symm

theorem singleSiteDoubledGate_su2Casimir (j : Fin n) :
    singleSiteDoubledGate j su2HermBasis.casimir =
      ((2 ^ n : ℂ) / 2) • (su2EmbHermBasis j).casimir := by
  change singleSiteDoubledGate j (∑ i : Fin 3, su2HermBasis.B i ⊗ₖ su2HermBasis.B i) =
    ((2 ^ n : ℂ) / 2) • ∑ i : Fin 3,
      (su2EmbHermBasis j).B i ⊗ₖ (su2EmbHermBasis j).B i
  change singleSiteDoubledGate j
      (∑ i ∈ Finset.univ, su2HermBasis.B i ⊗ₖ su2HermBasis.B i) =
    ((2 ^ n : ℂ) / 2) • ∑ i ∈ Finset.univ,
      (su2EmbHermBasis j).B i ⊗ₖ (su2EmbHermBasis j).B i
  rw [singleSiteDoubledGate_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← singleSiteDoubledGate_kronecker, singleSiteGate_su2B,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  congr 1
  calc
    (rt2inv * (rtNinv n)⁻¹) * (rt2inv * (rtNinv n)⁻¹)
        = (rt2inv * rt2inv) * ((rtNinv n)⁻¹ * (rtNinv n)⁻¹) := by ring
    _ = (2 ^ n : ℂ) / 2 := by
      rw [rt2inv_mul_self, rtNinv_inv_mul_self]
      ring

theorem productQubitClifford_twirl_localObs_eq (j : Fin n) :
    twirl2 (productQubitClifford (n := n))
        (pauliMat (siteP j 1) ⊗ₖ pauliMat (siteP j 1)) =
      ((2 ^ n : ℂ) / 3) • (su2EmbHermBasis j).casimir := by
  rw [← singleSiteGate_pauli (n := n) j 1, productQubitClifford_twirl_singleSite]
  change singleSiteDoubledGate j
      (twirl2 QubitTwoDesign.qubitClifford (pauliX ⊗ₖ pauliX)) =
    ((2 ^ n : ℂ) / 3) • (su2EmbHermBasis j).casimir
  rw [qubitClifford_twirl_pauliX, singleSiteDoubledGate_smul,
    singleSiteDoubledGate_su2Casimir, smul_smul]
  congr 1
  ring

theorem productQubitClifford_twirl_localObs (hn : 0 < n) :
    twirl2 (productQubitClifford (n := n)) (localObs hn ⊗ₖ localObs hn) =
      ((2 ^ n : ℂ) / 3) • (su2EmbHermBasis (⟨0, hn⟩ : Fin n)).casimir := by
  simpa [localObs] using
    productQubitClifford_twirl_localObs_eq (n := n) (⟨0, hn⟩ : Fin n)

end QuantumAlg
