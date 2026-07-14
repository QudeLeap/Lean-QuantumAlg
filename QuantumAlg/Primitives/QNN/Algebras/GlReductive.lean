/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import QuantumAlg.Primitives.QNN.Algebras.PauliStringSchur

/-!
# The honest reductive `gl(2ⁿ) = su(2ⁿ) ⊕ ℂ·1`

The full-controllability algebra `gl(2ⁿ)` is **not simple** — it is reductive,
`gl(2ⁿ) = su(2ⁿ) ⊕ ℂ·1` (traceless part `⊕` centre), so its doubled invariant space
`(g⊗g)^g = span{1, SWAP}` is genuinely **two**-dimensional and the single-Casimir Schur identity
`(g⊗g)^g = span{C}` is FALSE for `gl`. This file gives the honest, non-circular treatment via the
two-Casimir `RagoneReductive` decomposition into the two ideals:

* the traceless simple ideal `su(2ⁿ)` — the odd/non-identity Pauli strings, with the genuinely
  proved Schur identity `suHermBasis_schur`;
* the one-dimensional abelian centre `ℂ·1` — the normalized identity, whose Schur
  identity is trivial.

The reductive Ragone variance law then splits as `Var = P_su(ρ)·P_su(O)/dim su + P_c(ρ)·P_c(O)/1`.
For a **traceless** observable the centre term vanishes (`⟨1, O⟩ = 0`) and the
variance reduces to the
`su(2ⁿ)` law — this is why the exponential barren plateau is honestly stated on the traceless
`su(2ⁿ)` family and NOT on the full `gl(2ⁿ)`: with a general
(non-traceless) observable the centre/trace direction contributes an `O(1)` term, so `gl` full
controllability has no unconditional barren plateau. [RBS+23]
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The one-dimensional centre `ℂ·1` of `gl(2ⁿ)` -/

/-- The generator of the centre of `gl(2ⁿ)`: the (skew-Hermitian) identity `i·1`. -/
def centerGens (m : ℕ) : Set (Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :=
  {Complex.I • pauliMat (0 : Fin m → Fin 4)}

/-- Rescaling a nonzero scalar does not change a one-dimensional span. -/
private theorem span_singleton_smul_ne {m : ℕ} (a : ℂ) (ha : a ≠ 0)
    (P : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) :
    Submodule.span ℂ {a • P} = Submodule.span ℂ {P} := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  · exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩
  · exact Submodule.mem_span_singleton.mpr
      ⟨a⁻¹, by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]⟩

/-- **The centre `ℂ·1` of `gl(2ⁿ)` as a one-dimensional `DLAHermBasis`**: the normalized identity
`(1/√2ᵐ)·1` is its single Hermitian orthonormal basis vector. -/
noncomputable def centerHermBasis (m : ℕ) : DLAHermBasis (centerGens m) where
  dim := 1
  B := fun _ => rtNinv m • pauliMat (0 : Fin m → Fin 4)
  herm := fun _ => by rw [conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]
  ortho := fun i j => by
    rw [Subsingleton.elim i j, if_pos rfl, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply,
      rtNinv_conj, ← mul_assoc, rtNinv_mul_self, pauliMat_hsInner, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero m (by norm_num : (2 : ℂ) ≠ 0))]
  span_eq := by
    rw [Set.range_const, span_singleton_smul_ne (rtNinv m) (rtNinv_ne_zero m),
      dynamicalLieAlgebra,
      LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero
        (by rintro x rfl y rfl; exact lie_self _),
      centerGens, span_singleton_smul_ne Complex.I Complex.I_ne_zero]

@[simp] theorem centerHermBasis_dim (m : ℕ) : (centerHermBasis m).dim = 1 := rfl

/-- **The Schur identity is trivial for the centre.** On the one-dimensional centre the coefficient
matrix has no off-diagonal entries and a single diagonal entry, so `(g⊗g)^g = span{C}` directly from
the generic solver. -/
theorem centerHermBasis_schur (m : ℕ) :
    gTensorGInvariant (centerHermBasis m) = Submodule.span ℂ {(centerHermBasis m).casimir} := by
  haveI : Subsingleton (Fin (centerHermBasis m).dim) := by rw [centerHermBasis_dim]; infer_instance
  refine le_antisymm (fun X hX => ?_) (spanC_le_gTensorGInvariant _)
  exact gTensorGInvariant_le_spanC (centerHermBasis m) hX
    (fun a a' ha => absurd (Subsingleton.elim a a') ha)
    (fun a a' => by rw [Subsingleton.elim a a'])

/-! ### The two ideals `gl(2ⁿ⁺¹) = su(2ⁿ⁺¹) ⊕ centre` -/

/-- The two-ideal generator family of `gl(2ⁿ⁺¹)`: the traceless `su` ideal and the centre. -/
def glGens (n : ℕ) : Fin 2 → Set (Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ) :=
  Fin.cons (suGens (n + 1)) (Fin.cons (centerGens (n + 1)) Fin.elim0)

/-- The two-ideal Hermitian bases of `gl(2ⁿ⁺¹)` (a dependent family). -/
noncomputable def glBasis (n : ℕ) : (j : Fin 2) → DLAHermBasis (glGens n j) :=
  Fin.cons (α := fun j => DLAHermBasis (glGens n j)) (suHermBasis (n + 1))
    (Fin.cons (α := fun j => DLAHermBasis (glGens n j.succ)) (centerHermBasis (n + 1))
      (fun x => x.elim0))

@[simp] theorem glBasis_zero (n : ℕ) : glBasis n 0 = suHermBasis (n + 1) := rfl

@[simp] theorem glBasis_one (n : ℕ) : glBasis n 1 = centerHermBasis (n + 1) := rfl

/-- **`su`-strings are Hilbert–Schmidt orthogonal to the centre** (nonzero Pauli strings are
traceless, hence orthogonal to the identity). -/
theorem su_center_ortho (n : ℕ) (a : Fin (suHermBasis (n + 1)).dim)
    (b : Fin (centerHermBasis (n + 1)).dim) :
    hsInner ((suHermBasis (n + 1)).B a) ((centerHermBasis (n + 1)).B b) = 0 := by
  change hsInner (rtNinv (n + 1) • pauliMat (nzEquiv (n + 1) a).1)
      (rtNinv (n + 1) • pauliMat (0 : Fin (n + 1) → Fin 4)) = 0
  rw [hsInner_smul_left, hsInner_smul_right, pauliMat_hsInner, if_neg (nzEquiv (n + 1) a).2,
    mul_zero, mul_zero]

/-- The two ideals of `gl(2ⁿ⁺¹)` are mutually Hilbert–Schmidt orthogonal. -/
theorem gl_cross_ortho (n : ℕ) : ∀ (i j : Fin 2), i ≠ j →
    ∀ (a : Fin (glBasis n i).dim) (b : Fin (glBasis n j).dim),
      hsInner ((glBasis n i).B a) ((glBasis n j).B b) = 0 := by
  intro i j hij a b
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact su_center_ortho n a b
  · change hsInner ((centerHermBasis (n + 1)).B a) ((suHermBasis (n + 1)).B b) = 0
    rw [hsInner_comm_of_isHermitian ((centerHermBasis (n + 1)).herm a)
        ((suHermBasis (n + 1)).herm b), su_center_ortho n b a]
  · exact absurd rfl hij

/-! ### The reductive `gl(2ⁿ⁺¹)` bundle and honest variance law -/

/-- The Hermitian witness operator for the `gl` reductive bundle: the first (**traceless**) `su`
basis element, used for both slots of the bilinear variance law. -/
noncomputable def glObs (n : ℕ) : Matrix (Fin (2 ^ (n + 1))) (Fin (2 ^ (n + 1))) ℂ :=
  (suHermBasis (n + 1)).B (suI0 n)

theorem glObs_isHermitian (n : ℕ) : (glObs n)ᴴ = glObs n := (suHermBasis (n + 1)).herm (suI0 n)

/-- **The reductive `gl(2ⁿ⁺¹) = su ⊕ centre` bundle.** Both per-ideal Schur identities are genuinely
proved (`suHermBasis_schur` for the simple part, `centerHermBasis_schur` for the
centre); the diagonal
second moment discharges the per-ideal diagonal memberships and the cross-ideal invariant-block
exclusion non-circularly. No false single-Casimir hypothesis is posited. -/
noncomputable def glReductive (n : ℕ) : RagoneReductive (glObs n) (glObs n) :=
  RagoneReductive.consistencyWitness 2
    (glGens n)
    (glBasis n)
    (gl_cross_ortho n)
    (glObs_isHermitian n) (glObs_isHermitian n)
    (by intro j; fin_cases j
        · exact suHermBasis_dim_pos n
        · exact Nat.one_pos)
    (by intro j; fin_cases j
        · exact suHermBasis_schur (n + 1)
        · exact centerHermBasis_schur (n + 1))

/-- **The honest reductive `gl(2ⁿ⁺¹)` variance law.** By
`RagoneReductive.totalVariance_eq` the total
variance is the two-Casimir sum `P_su(ρ)·P_su(O)/dim su + P_c(ρ)·P_c(O)/1`. With
`ρ = O` the traceless
first `su`-basis element (`P_su = 1`, `P_c = 0` by cross-orthogonality), the
centre term vanishes and
the sum collapses to the `su` term `1 / dim su(2ⁿ⁺¹) = 1 / (4ⁿ⁺¹ − 1)` — the honest exponentially
small variance, carried by the traceless simple ideal, not by the full `gl`. [RBS+23] -/
theorem glReductive_totalVariance_eq (n : ℕ) :
    ((glReductive n).variance : ℂ) = 1 / ((suHermBasis (n + 1)).dim : ℂ) := by
  have hpos : ∀ j, 0 < ((glReductive n).basis j).dim := by
    intro j; fin_cases j
    · exact suHermBasis_dim_pos n
    · exact Nat.one_pos
  rw [(glReductive n).totalVariance_eq (glObs_isHermitian n) (glObs_isHermitian n) hpos]
  change (∑ j : Fin 2, (glBasis n j).gPurity (glObs n)
      * (glBasis n j).gPurity (glObs n) / ((glBasis n j).dim : ℂ)) = _
  have hsu1 : (glBasis n 0).gPurity (glObs n) = 1 :=
    DLAHermBasis.gPurity_basis_elem (glBasis n 0) (suI0 n)
  have hpc : (glBasis n 1).gPurity (glObs n) = 0 := by
    rw [DLAHermBasis.gPurity]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hz : hsInner ((glBasis n 1).B a) (glObs n) = 0 := by
      change hsInner ((centerHermBasis (n + 1)).B a) ((suHermBasis (n + 1)).B (suI0 n)) = 0
      rw [hsInner_comm_of_isHermitian ((centerHermBasis (n + 1)).herm a)
          ((suHermBasis (n + 1)).herm (suI0 n)), su_center_ortho n (suI0 n) a]
    rw [hz]; simp
  rw [Fin.sum_univ_two, hsu1, hpc]
  simp [glBasis_zero]

/-- Corollary-style `base > 2` barren-plateau witness for the traceless simple ideal in the
honest reductive full-controllability treatment. The proof uses the Hilbert-Schmidt-norm
capstone, with both Hermitian witness operators chosen as a normalized `su(2^(n+1))` basis element.
-/
theorem fullControllability_hasBarrenPlateau_b2 :
    HasBarrenPlateau (fun n => (suSM n (suHermBasis_schur (n + 1))).variance) := by
  refine ragone_hasBarrenPlateau_hsNorm
    (M := fun n => suSM n (suHermBasis_schur (n + 1)))
    (hρ := fun n => (suHermBasis (n + 1)).herm (suI0 n))
    (hO := fun n => (suHermBasis (n + 1)).herm (suI0 n))
    (hdimpos := fun n => suHermBasis_dim_pos n)
    (hρnorm := fun n => ?_)
    (hOnorm := fun n => ?_)
    (base := 3) (by norm_num) ?_
  · rw [(suHermBasis (n + 1)).ortho (suI0 n) (suI0 n), if_pos rfl]
    norm_num
  · calc (hsInner ((suHermBasis (n + 1)).B (suI0 n))
        ((suHermBasis (n + 1)).B (suI0 n))).re
        = 1 := by
          rw [(suHermBasis (n + 1)).ortho (suI0 n) (suI0 n), if_pos rfl]
          norm_num
      _ ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  · intro n
    have h3le4 : (3 : ℕ) ^ n ≤ 4 ^ n :=
      pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 3) (by norm_num : (3 : ℕ) ≤ 4) n
    have h4pos : 1 ≤ 4 ^ n := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 4)
    have hsucc : 4 ^ n + 1 ≤ 4 ^ (n + 1) := by
      calc 4 ^ n + 1 ≤ 4 ^ n + 3 * 4 ^ n := by nlinarith
        _ = 4 ^ (n + 1) := by
          rw [pow_succ]
          ring
    have hdim : 4 ^ n ≤ 2 ^ (n + 1) * 2 ^ (n + 1) - 1 := by
      have hprod : 2 ^ (n + 1) * 2 ^ (n + 1) = 4 ^ (n + 1) := by
        rw [← mul_pow]
        norm_num
      rw [hprod]
      omega
    exact_mod_cast h3le4.trans hdim

/-- Non-vacuity of the reductive full-controllability bundle, anchored on the honest
`gl = su ⊕ center` construction. -/
theorem ragone_reductive_nonempty_gl2 :
    Nonempty (RagoneReductive (glObs 1) (glObs 1)) :=
  ⟨glReductive 1⟩

end QuantumAlg
