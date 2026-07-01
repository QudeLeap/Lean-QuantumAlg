/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.FullDLABasis
public import QuantumAlg.Util.Haar

/-!
# Simple dynamical Lie algebras `g ≃ su(d)`: single-ideal variance and the barren plateau

For a circuit whose dynamical Lie algebra is **simple** with `g ≃ su(d)` (dimension `d² − 1`,
centerless), the reductive variance sum collapses to a single term and the loss-gradient variance is
`Var_θ[ℓ] = P_g(ρ) · P_g(O) / (d² − 1)` [RBS+23, Arxiv_Final.tex:691]. In particular, for `d = 2ⁿ`
the dimension `4ⁿ − 1` grows exponentially, so the loss exhibits an exponential barren plateau —
the seminal `su(2ⁿ)` case.

The abstract reduction (`SimpleSU.main`) holds for any Hermitian
Hilbert–Schmidt orthonormal basis of the simple dimension `d² − 1`; it is
genuinely **witnessed** here by the explicit `su(2)` algebra
(`su2HermBasis`, dimension `3`), built from the Pauli matrices with their commutation relations
`[X, Y] = 2i Z`, etc. The deep Haar/Schur per-ideal second-moment projection remains the named
hypothesis of `RagoneSecondMoment` — everything here is downstream of the proved variance formula.

The genuine general-`d` construction (`su(2ⁿ)` for all `n`, via a traceless Gell-Mann basis) is the
remaining work; here the `su(2)` witness already discharges the non-vacuity of the simple case.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Pauli commutation relations -/

/-- `[X, Y] = 2i Z`. -/
theorem lie_pauliX_pauliY : ⁅pauliX, pauliY⁆ = (2 * Complex.I) • pauliZ := by
  rw [Ring.lie_def, pauliX, pauliY, pauliZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] <;>
    ring_nf

/-- `[Y, Z] = 2i X`. -/
theorem lie_pauliY_pauliZ : ⁅pauliY, pauliZ⁆ = (2 * Complex.I) • pauliX := by
  rw [Ring.lie_def, pauliX, pauliY, pauliZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] <;>
    ring_nf

/-- `[Z, X] = 2i Y`. -/
theorem lie_pauliZ_pauliX : ⁅pauliZ, pauliX⁆ = (2 * Complex.I) • pauliY := by
  rw [Ring.lie_def, pauliX, pauliY, pauliZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul] <;>
    ring_nf
  · rw [Complex.I_sq]
    ring
  · rw [Complex.I_sq]
    ring

/-! ### The Pauli matrices are Hermitian -/

theorem pauliX_isHermitian : pauliXᴴ = pauliX := by
  rw [pauliX]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

theorem pauliY_isHermitian : pauliYᴴ = pauliY := by
  rw [pauliY]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Complex.conj_I]

theorem pauliZ_isHermitian : pauliZᴴ = pauliZ := by
  rw [pauliZ]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

/-! ### `su(2)`: the complex span of `{X, Y, Z}` is the DLA, and a Lie subalgebra -/

/-- The Hermitian Pauli generating set `{X, Y, Z}`. -/
def su2Set : Set (Matrix (Fin 2) (Fin 2) ℂ) := {pauliX, pauliY, pauliZ}

/-- The skew-Hermitian circuit generators `{iX, iY, iZ}` of an `su(2)` dynamical Lie algebra. -/
def su2Gens : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {Complex.I • pauliX, Complex.I • pauliY, Complex.I • pauliZ}

theorem pauliX_mem_su2Set : pauliX ∈ su2Set := by
  simp [su2Set]
theorem pauliY_mem_su2Set : pauliY ∈ su2Set := by
  simp [su2Set]
theorem pauliZ_mem_su2Set : pauliZ ∈ su2Set := by
  simp [su2Set]

/-- The bracket of two `su(2)` generators lands in `span ℂ {X, Y, Z}`: closure of the span. -/
theorem su2_lie_mem_span ⦃x y : Matrix (Fin 2) (Fin 2) ℂ⦄
    (hx : x ∈ Submodule.span ℂ su2Set) (hy : y ∈ Submodule.span ℂ su2Set) :
    ⁅x, y⁆ ∈ Submodule.span ℂ su2Set := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      -- both generators: the nine Pauli brackets
      simp only [su2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      have hX : pauliX ∈ Submodule.span ℂ su2Set := Submodule.subset_span pauliX_mem_su2Set
      have hY : pauliY ∈ Submodule.span ℂ su2Set := Submodule.subset_span pauliY_mem_su2Set
      have hZ : pauliZ ∈ Submodule.span ℂ su2Set := Submodule.subset_span pauliZ_mem_su2Set
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | (rw [lie_self]; exact zero_mem _)
          | (rw [lie_pauliX_pauliY]; exact Submodule.smul_mem _ _ hZ)
          | (rw [lie_pauliY_pauliZ]; exact Submodule.smul_mem _ _ hX)
          | (rw [lie_pauliZ_pauliX]; exact Submodule.smul_mem _ _ hY)
          | (rw [← lie_skew, lie_pauliX_pauliY]; exact neg_mem (Submodule.smul_mem _ _ hZ))
          | (rw [← lie_skew, lie_pauliY_pauliZ]; exact neg_mem (Submodule.smul_mem _ _ hX))
          | (rw [← lie_skew, lie_pauliZ_pauliX]; exact neg_mem (Submodule.smul_mem _ _ hY))
    | zero => rw [lie_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [lie_add]; exact add_mem hb hc
    | smul r b _ hb => rw [lie_smul]; exact Submodule.smul_mem _ _ hb
  | zero => rw [zero_lie]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_lie]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_lie]; exact Submodule.smul_mem _ _ ha

/-- `span ℂ {X, Y, Z}` as a Lie subalgebra of `gl(2, ℂ)` — the complexification of `su(2)`. -/
def su2Lie : LieSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ) where
  toSubmodule := Submodule.span ℂ su2Set
  lie_mem' := fun hx hy => su2_lie_mem_span hx hy

theorem su2Gens_subset_su2Lie : su2Gens ⊆ (su2Lie : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  intro a ha
  simp only [su2Gens, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  have hmem : ∀ P ∈ su2Set, Complex.I • P ∈ su2Lie := by
    intro P hP
    change Complex.I • P ∈ Submodule.span ℂ su2Set
    exact Submodule.smul_mem _ Complex.I (Submodule.subset_span hP)
  rcases ha with rfl | rfl | rfl
  · exact hmem _ pauliX_mem_su2Set
  · exact hmem _ pauliY_mem_su2Set
  · exact hmem _ pauliZ_mem_su2Set

/-- The dynamical Lie algebra of `{iX, iY, iZ}` is, as a submodule, `span ℂ {X, Y, Z}`. -/
theorem su2_dla_toSubmodule :
    (dynamicalLieAlgebra su2Gens).toSubmodule = Submodule.span ℂ su2Set := by
  apply le_antisymm
  · -- DLA ⊆ span{X,Y,Z}: minimality against the Lie subalgebra `su2Lie`
    intro x hx
    exact dynamicalLieAlgebra_minimal su2Gens su2Gens_subset_su2Lie hx
  · -- span{X,Y,Z} ⊆ DLA: each Pauli is `-i` times a generator
    rw [Submodule.span_le]
    intro a ha
    simp only [su2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hgen : su2Gens ⊆ (dynamicalLieAlgebra su2Gens : Set _) :=
      generators_subset_dynamicalLieAlgebra su2Gens
    have hPauli : ∀ P ∈ su2Gens, (-Complex.I) • P ∈ dynamicalLieAlgebra su2Gens := fun P hP =>
      Submodule.smul_mem _ _ (hgen hP)
    have key : ∀ P : Matrix (Fin 2) (Fin 2) ℂ, (-Complex.I) • (Complex.I • P) = P := by
      intro P; rw [smul_smul]; simp [Complex.I_mul_I]
    rcases ha with rfl | rfl | rfl
    · have := hPauli _ (show Complex.I • pauliX ∈ su2Gens by simp [su2Gens]); rwa [key] at this
    · have := hPauli _ (show Complex.I • pauliY ∈ su2Gens by simp [su2Gens]); rwa [key] at this
    · have := hPauli _ (show Complex.I • pauliZ ∈ su2Gens by simp [su2Gens]); rwa [key] at this

/-! ### The `su(2)` Hermitian orthonormal basis -/

/-- The three normalized Hermitian Pauli basis vectors `{X, Y, Z}/√2`. -/
noncomputable def su2B : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![rt2inv • pauliX, rt2inv • pauliY, rt2inv • pauliZ]

theorem su2_range_span : Submodule.span ℂ (Set.range su2B) = Submodule.span ℂ su2Set := by
  have hrt : rt2inv ≠ 0 := by
    intro h; have h2 := rt2inv_mul_self; rw [h, mul_zero] at h2; norm_num at h2
  have key : ∀ P : Matrix (Fin 2) (Fin 2) ℂ, rt2inv⁻¹ • (rt2inv • P) = P := fun P => by
    rw [smul_smul, inv_mul_cancel₀ hrt, one_smul]
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    fin_cases i
    · exact Submodule.smul_mem _ rt2inv (Submodule.subset_span pauliX_mem_su2Set)
    · exact Submodule.smul_mem _ rt2inv (Submodule.subset_span pauliY_mem_su2Set)
    · exact Submodule.smul_mem _ rt2inv (Submodule.subset_span pauliZ_mem_su2Set)
  · rw [Submodule.span_le]
    intro a ha
    simp only [su2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    have hmem : ∀ k : Fin 3, su2B k ∈ Submodule.span ℂ (Set.range su2B) := fun k =>
      Submodule.subset_span ⟨k, rfl⟩
    rcases ha with rfl | rfl | rfl
    · have h0 := Submodule.smul_mem (Submodule.span ℂ (Set.range su2B)) rt2inv⁻¹ (hmem 0)
      rw [show su2B 0 = rt2inv • pauliX from rfl, key] at h0; exact h0
    · have h1 := Submodule.smul_mem (Submodule.span ℂ (Set.range su2B)) rt2inv⁻¹ (hmem 1)
      rw [show su2B 1 = rt2inv • pauliY from rfl, key] at h1; exact h1
    · have h2 := Submodule.smul_mem (Submodule.span ℂ (Set.range su2B)) rt2inv⁻¹ (hmem 2)
      rw [show su2B 2 = rt2inv • pauliZ from rfl, key] at h2; exact h2

/-- The Hermitian orthonormality of the normalized Pauli basis (`Tr[Pᴴ Q] = 2 δ`,
so `⟪P/√2, Q/√2⟫ = δ`). -/
theorem su2B_ortho (i j : Fin 3) : hsInner (su2B i) (su2B j) = if i = j then 1 else 0 := by
  have key : ∀ P Q : Matrix (Fin 2) (Fin 2) ℂ,
      hsInner (rt2inv • P) (rt2inv • Q) = (1 / 2 : ℂ) * hsInner P Q := fun P Q => by
    rw [hsInner_smul_left, hsInner_smul_right, ← mul_assoc, starRingEnd_apply, rt2inv_conj,
      rt2inv_mul_self]
  have fin2 : ∀ P Q : Matrix (Fin 2) (Fin 2) ℂ, Pᴴ = P →
      hsInner (rt2inv • P) (rt2inv • Q) = (1 / 2 : ℂ) * (P * Q).trace := by
    intro P Q hP; rw [key, hsInner, hP]
  fin_cases i <;> fin_cases j
  · change hsInner (rt2inv • pauliX) (rt2inv • pauliX) = 1
    rw [fin2 _ _ pauliX_isHermitian]; norm_num [pauliX, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliX) (rt2inv • pauliY) = 0
    rw [fin2 _ _ pauliX_isHermitian]
    norm_num [pauliX, pauliY, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliX) (rt2inv • pauliZ) = 0
    rw [fin2 _ _ pauliX_isHermitian]
    norm_num [pauliX, pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliY) (rt2inv • pauliX) = 0
    rw [fin2 _ _ pauliY_isHermitian]
    norm_num [pauliX, pauliY, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliY) (rt2inv • pauliY) = 1
    rw [fin2 _ _ pauliY_isHermitian]
    norm_num [pauliY, Matrix.mul_fin_two, Matrix.trace_fin_two, Complex.I_mul_I]
  · change hsInner (rt2inv • pauliY) (rt2inv • pauliZ) = 0
    rw [fin2 _ _ pauliY_isHermitian]
    norm_num [pauliY, pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliZ) (rt2inv • pauliX) = 0
    rw [fin2 _ _ pauliZ_isHermitian]
    norm_num [pauliX, pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliZ) (rt2inv • pauliY) = 0
    rw [fin2 _ _ pauliZ_isHermitian]
    norm_num [pauliY, pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  · change hsInner (rt2inv • pauliZ) (rt2inv • pauliZ) = 1
    rw [fin2 _ _ pauliZ_isHermitian]; norm_num [pauliZ, Matrix.mul_fin_two, Matrix.trace_fin_two]

theorem su2B_isHermitian (i : Fin 3) : (su2B i)ᴴ = su2B i := by
  fin_cases i
  · change (rt2inv • pauliX)ᴴ = rt2inv • pauliX
    rw [Matrix.conjTranspose_smul, rt2inv_conj, pauliX_isHermitian]
  · change (rt2inv • pauliY)ᴴ = rt2inv • pauliY
    rw [Matrix.conjTranspose_smul, rt2inv_conj, pauliY_isHermitian]
  · change (rt2inv • pauliZ)ᴴ = rt2inv • pauliZ
    rw [Matrix.conjTranspose_smul, rt2inv_conj, pauliZ_isHermitian]

/-- **The genuine `su(2)` dynamical Lie algebra as a `DLAHermBasis`** (dimension `3 = 2² − 1`),
built from the Pauli matrices with `[X,Y]=2iZ`, etc. This is the smallest simple, centerless DLA,
witnessing the `g ≃ su(d)` hypothesis non-vacuously. -/
noncomputable def su2HermBasis : DLAHermBasis su2Gens where
  dim := 3
  B := su2B
  herm := su2B_isHermitian
  ortho := su2B_ortho
  span_eq := by rw [su2_range_span, su2_dla_toSubmodule]

/-! ### The simple-`su(d)` variance reduction and the barren plateau -/

namespace SimpleSU

variable {N : ℕ}

/-- **The `g ≃ su(d)` loss-variance reduction.** If a dynamical Lie algebra has a Hermitian
Hilbert–Schmidt orthonormal basis `b` of the simple dimension `dim g = d² − 1` (i.e. `g ≃ su(d)`),
then — under the Haar second-moment bundle and Hermitian `ρ`, `O` — the loss variance collapses to
the single term `Var_θ[ℓ] = P_g(ρ) · P_g(O) / (d² − 1)` [RBS+23, Arxiv_Final.tex:691]. Downstream of
the proved `variance_eq_gPurity`; the Haar/Schur projection stays the named hypothesis. -/
theorem main {gens : Set (Matrix (Fin N) (Fin N) ℂ)} {b : DLAHermBasis gens}
    {ρ O : Matrix (Fin N) (Fin N) ℂ} (M : RagoneSecondMoment b ρ O)
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O) {d : ℕ} (hd : b.dim = d * d - 1) (hpos : 0 < b.dim) :
    (M.variance : ℂ) = b.gPurity ρ * b.gPurity O / ((d * d - 1 : ℕ) : ℂ) := by
  rw [M.variance_eq_gPurity hρ hO hpos, hd]

/-- **The simple `su(2ⁿ)` exponential barren plateau.** For a qubit-indexed family of simple
dynamical Lie algebras with `dim gₙ = (2ⁿ⁺¹)² − 1 = 4ⁿ⁺¹ − 1` (the `su(2ⁿ⁺¹)` dimension, reindexed
so the dimension is positive at every `n`), bounded `g`-purity numerator, and the Haar second-moment
bundle, the loss has an exponential barren plateau. The dimension `4ⁿ⁺¹ − 1` grows faster than `2ⁿ`,
so this is a genuine consequence of the proved variance formula [RBS+23, Arxiv_Final.tex:691]. -/
theorem main_barren_plateau {sz : ℕ → ℕ}
    {gens : (n : ℕ) → Set (Matrix (Fin (sz n)) (Fin (sz n)) ℂ)}
    {ρ O : (n : ℕ) → Matrix (Fin (sz n)) (Fin (sz n)) ℂ}
    {b : (n : ℕ) → DLAHermBasis (gens n)}
    (M : (n : ℕ) → RagoneSecondMoment (b n) (ρ n) (O n))
    (hρ : ∀ n, (ρ n)ᴴ = ρ n) (hO : ∀ n, (O n)ᴴ = O n)
    (hdim : ∀ n, (b n).dim = 2 ^ (n + 1) * 2 ^ (n + 1) - 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ n, ‖(b n).gPurity (ρ n) * (b n).gPurity (O n)‖ ≤ C) :
    HasBarrenPlateau (fun n => (M n).variance) := by
  refine ragone_hasBarrenPlateau M hρ hO ?_ hC hbound (base := 2) one_lt_two ?_
  · intro n
    rw [hdim n]
    have h1lt : 1 < 2 ^ (n + 1) :=
      lt_of_lt_of_le one_lt_two (Nat.le_self_pow (Nat.succ_ne_zero n) 2)
    have hX : 1 < 2 ^ (n + 1) * 2 ^ (n + 1) := by nlinarith [h1lt]
    omega
  · intro n
    have hnat : 2 ^ n ≤ 2 ^ (n + 1) * 2 ^ (n + 1) - 1 := by
      have h1 : 2 ^ n ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n)
      have h1lt : 1 < 2 ^ (n + 1) :=
        lt_of_lt_of_le one_lt_two (Nat.le_self_pow (Nat.succ_ne_zero n) 2)
      have hX : 2 ^ n + 1 ≤ 2 ^ (n + 1) * 2 ^ (n + 1) := by nlinarith [h1, h1lt]
      omega
    rw [hdim n]
    exact_mod_cast hnat

end SimpleSU

/-! ### Non-vacuity: the `su(2)` witness -/

theorem su2HermBasis_dim_pos : 0 < su2HermBasis.dim := by
  change (0 : ℕ) < 3
  norm_num

/-- The index of the first `su(2)` basis element. -/
def su2i0 : Fin su2HermBasis.dim := ⟨0, su2HermBasis_dim_pos⟩

/-- The `su(2)` second-moment bundle with state and observable the first basis element. -/
noncomputable def su2SM :
    RagoneSecondMoment su2HermBasis (su2HermBasis.B su2i0) (su2HermBasis.B su2i0) :=
  RagoneSecondMoment.ofHermitian (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0)
    su2HermBasis_dim_pos

/-- **Non-vacuity of `SimpleSU.main`.** The `su(2)` algebra (dimension `3 = 2² − 1`) genuinely
satisfies the `g ≃ su(d)` reduction: its loss variance is `P_g(ρ)·P_g(O)/3`. With `ρ = O = X/√2`
(a normalized basis element, `P_g = 1`) this evaluates to `1/3`. -/
theorem su2_variance_eq :
    (su2SM.variance : ℂ)
      = su2HermBasis.gPurity (su2HermBasis.B su2i0)
          * su2HermBasis.gPurity (su2HermBasis.B su2i0) / ((2 * 2 - 1 : ℕ) : ℂ) :=
  SimpleSU.main su2SM (su2HermBasis.herm su2i0) (su2HermBasis.herm su2i0)
    (d := 2) rfl su2HermBasis_dim_pos

theorem su2_variance_eq_third : (su2SM.variance : ℂ) = 1 / 3 := by
  rw [su2_variance_eq, su2HermBasis.gPurity_basis_elem su2i0]; norm_num

end QuantumAlg
