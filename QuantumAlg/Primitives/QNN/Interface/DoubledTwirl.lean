/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Interface.RagoneInterface
public import QuantumAlg.Util.Haar

/-!
# The genuine finite `t = 2`-design doubled twirl

The Ragone second moment is the `t = 2` twirl `M²(O⊗O)` of `O ⊗ O` over the dynamical Lie group.
Here we build the **genuine** doubled twirl as the finite-group average

  `twirl₂ u X = (1/|G|) Σ_{g∈G} (u g ⊗ₖ u g) · X · (u g ⊗ₖ u g)ᴴ`

over a finite gate group `G` acting through a unitary representation `u`. It is literally
`repTwirl (doubledRep u)` on the doubled operator space, so its projection/idempotence/commutation/
trace properties are inherited for free from `QuantumAlg.Util.Haar` once the doubled representation
`doubledRep u g = u g ⊗ₖ u g` is shown to be a unitary representation.

From this we discharge the `var_eq` and `proj_orth` fields of `RagoneSecondMoment` **from the twirl
mechanism** (rather than hand-setting `secondMoment := κ • C` as `consistencyWitness` does): the
`ofTwoDesign` witness sets `secondMoment := twirl₂ u (O ⊗ₖ O)`.

The remaining deep inputs stay isolated as named hypotheses, never `sorry`:
* **`mem_invariant`** is *not* twirl-derived. The twirl lands in the **finite-group** doubled
  commutant (commutes with every `u V ⊗ₖ u V`), whereas `adCommutantGG` is the **Lie-algebra**
  commutant. Bridging them is the *commutant-completeness* property of a genuine `2`-design (the
  group commutant equals the connected-DLA-group commutant) — kept as a named hypothesis, together
  with the carrier hypothesis that the twirl lands in `g ⊗ g`. (NB: commutants are
  inclusion-*reversing*, so this is genuinely deep, not the naive exp-correspondence.)
* **`invariant_eq_spanC`** (Schur, H2) stays deferred, as in `RagoneInterface`.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Kronecker

attribute [local instance 100] LieRing.ofAssociativeRing

variable {N : ℕ} {G : Type*} [Group G] [Fintype G]

/-- The **doubled representation** `g ↦ u g ⊗ₖ u g` on the doubled operator space. -/
noncomputable def doubledRep (u : G → Matrix (Fin N) (Fin N) ℂ) (g : G) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := u g ⊗ₖ u g

/-- The **doubled (`t = 2`) twirl**: the finite-group average of `(u g ⊗ u g) · X · (u g ⊗ u g)ᴴ`,
i.e. `repTwirl` of the doubled representation on the doubled operator space. -/
noncomputable def twirl2 (u : G → Matrix (Fin N) (Fin N) ℂ)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  repTwirl (doubledRep u) X

omit [Fintype G] in
/-- The doubled representation is multiplicative (a group homomorphism into matrices). -/
theorem doubledRep_mul (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (a b : G) :
    doubledRep u (a * b) = doubledRep u a * doubledRep u b := by
  simp only [doubledRep, hmul, Matrix.mul_kronecker_mul]

omit [Group G] [Fintype G] in
/-- The doubled representation is unitary: `(u g ⊗ u g)ᴴ (u g ⊗ u g) = 1`. -/
theorem doubledRep_unit (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hunit : ∀ a, (u a)ᴴ * u a = 1) (a : G) :
    (doubledRep u a)ᴴ * doubledRep u a = 1 := by
  simp only [doubledRep, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hunit,
    Matrix.one_kronecker_one]

/-- **The doubled twirl lands in the finite-group commutant** (free from `repTwirl_commute`). -/
theorem twirl2_commute (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) (V : G) :
    (u V ⊗ₖ u V) * twirl2 u X = twirl2 u X * (u V ⊗ₖ u V) :=
  repTwirl_commute (doubledRep u) (doubledRep_mul u hmul) (doubledRep_unit u hunit) X V

/-- **The doubled twirl is idempotent** (a projection; free from `repTwirl_idem`). -/
theorem twirl2_idem (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    twirl2 u (twirl2 u X) = twirl2 u X :=
  repTwirl_idem (doubledRep u) (doubledRep_mul u hmul) X

/-- **The doubled twirl preserves the trace** (free from `repTwirl_trace`). -/
theorem twirl2_trace (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hunit : ∀ a, (u a)ᴴ * u a = 1)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    (twirl2 u X).trace = X.trace :=
  repTwirl_trace (doubledRep u) (doubledRep_unit u hunit) X

omit [Group G] in
/-- The doubled twirl is the finite average of the doubled conjugations `doubledConj (u g)`. -/
theorem twirl2_eq_sum_doubledConj (u : G → Matrix (Fin N) (Fin N) ℂ)
    (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    twirl2 u X = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, doubledConj (u g) X := by
  simp only [twirl2, repTwirl, doubledConj, doubledRep]

omit [Group G] in
/-- The doubled twirl is homogeneous in its matrix argument. -/
theorem twirl2_smul (u : G → Matrix (Fin N) (Fin N) ℂ)
    (c : ℂ) (X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    twirl2 u (c • X) = c • twirl2 u X := by
  unfold twirl2 repTwirl
  have hterm :
      ∀ g : G, doubledRep u g * (c • X) * (doubledRep u g)ᴴ =
        c • (doubledRep u g * X * (doubledRep u g)ᴴ) := by
    intro g
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [Finset.sum_congr rfl (fun g _ => hterm g), ← Finset.smul_sum]
  module

omit [Group G] [Fintype G] in
/-- The Hilbert--Schmidt pairing of doubled pure tensor inputs is the squared trace pairing. -/
theorem hsInner_kronecker_trace_sq (ρ A : Matrix (Fin N) (Fin N) ℂ) (hρ : ρᴴ = ρ) :
    hsInner (ρ ⊗ₖ ρ) (A ⊗ₖ A) = ((ρ * A).trace) ^ 2 := by
  simp only [hsInner, Matrix.conjTranspose_kronecker, hρ]
  rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  ring

omit [Group G] in
/-- Pairing a doubled input against the finite doubled twirl gives the empirical loss
second moment. -/
theorem twirl2_hsInner_eq_loss_secondMoment (u : G → Matrix (Fin N) (Fin N) ℂ)
    (ρ O : Matrix (Fin N) (Fin N) ℂ) (hρ : ρᴴ = ρ) :
    hsInner (ρ ⊗ₖ ρ) (twirl2 u (O ⊗ₖ O)) =
      (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, ((ρ * (u g * O * (u g)ᴴ)).trace) ^ 2 := by
  unfold twirl2 repTwirl doubledRep
  rw [hsInner_smul_right, hsInner_sum_right]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [← Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  exact hsInner_kronecker_trace_sq ρ (u g * O * (u g)ᴴ) hρ

/-! ### Unitary-representation prerequisites -/

omit [Fintype G] in
/-- A unitary representation sends `1` to `1`. -/
theorem u_one (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1) :
    u 1 = 1 := by
  have h : u 1 * u 1 = u 1 := by rw [← hmul, mul_one]
  calc u 1 = (u 1)ᴴ * u 1 * u 1 := by rw [hunit, Matrix.one_mul]
    _ = (u 1)ᴴ * (u 1 * u 1) := by rw [Matrix.mul_assoc]
    _ = (u 1)ᴴ * u 1 := by rw [h]
    _ = 1 := hunit 1

omit [Fintype G] in
/-- The doubled representation sends `1` to `1`. -/
theorem doubledRep_one (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1) :
    doubledRep u 1 = 1 := by
  rw [doubledRep, u_one u hmul hunit, Matrix.one_kronecker_one]

omit [Group G] [Fintype G] in
/-- Right unitarity of the doubled representation (the two-sided twin of `doubledRep_unit`). -/
theorem doubledRep_unit' (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hunit : ∀ a, (u a)ᴴ * u a = 1) (a : G) :
    doubledRep u a * (doubledRep u a)ᴴ = 1 :=
  mul_eq_one_comm.mp (doubledRep_unit u hunit a)

omit [Fintype G] in
/-- The conjugate transpose of the doubled representation is its value at the inverse. -/
theorem doubledRep_conjTranspose_eq_inv (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1) (g : G) :
    (doubledRep u g)ᴴ = doubledRep u g⁻¹ := by
  have h1 : doubledRep u g⁻¹ * doubledRep u g = 1 := by
    rw [← doubledRep_mul u hmul, inv_mul_cancel, doubledRep_one u hmul hunit]
  calc (doubledRep u g)ᴴ
      = doubledRep u g⁻¹ * doubledRep u g * (doubledRep u g)ᴴ := by rw [h1, Matrix.one_mul]
    _ = doubledRep u g⁻¹ * (doubledRep u g * (doubledRep u g)ᴴ) := by rw [Matrix.mul_assoc]
    _ = doubledRep u g⁻¹ := by rw [doubledRep_unit' u hunit, Matrix.mul_one]

/-! ### Genuine-twirl helpers: Hermiticity, HS self-adjointness, Casimir-fixing -/

omit [Group G] in
/-- **The doubled twirl preserves Hermiticity.** -/
theorem twirl2_isHermitian_of (u : G → Matrix (Fin N) (Fin N) ℂ)
    {X : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ} (hX : Xᴴ = X) :
    (twirl2 u X)ᴴ = twirl2 u X := by
  simp only [twirl2, repTwirl, conjTranspose_smul, conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hX, star_inv₀, star_natCast, Matrix.mul_assoc]

/-- **The doubled twirl is self-adjoint for the Hilbert–Schmidt inner product.** This is the
load-bearing fact for `proj_orth`: each conjugation `v · vᴴ` moves across `⟪·,·⟫` to its adjoint
`vᴴ · v`, and averaging over the (inverse-closed) group sends `vᴴ · v` back to `v · vᴴ` by the
`g ↦ g⁻¹` reindexing. -/
theorem twirl2_hsInner_selfAdjoint (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1)
    (X Y : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) :
    hsInner (twirl2 u X) Y = hsInner X (twirl2 u Y) := by
  -- per-conjugation adjoint move (pure trace cyclicity, any v)
  have hpg0 : ∀ v : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
      hsInner (v * X * vᴴ) Y = hsInner X (vᴴ * Y * v) := by
    intro v
    simp only [hsInner, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm v]
    simp only [Matrix.mul_assoc]
  -- reindex g ↦ g⁻¹ turns the adjoint conjugation back into the forward one
  have hreidx : (∑ g : G, hsInner X ((doubledRep u g)ᴴ * Y * doubledRep u g))
      = ∑ g : G, hsInner X (doubledRep u g * Y * (doubledRep u g)ᴴ) := by
    have hF : ∀ g : G, hsInner X (doubledRep u g⁻¹ * Y * (doubledRep u g⁻¹)ᴴ)
        = hsInner X ((doubledRep u g)ᴴ * Y * doubledRep u g) := by
      intro g
      rw [doubledRep_conjTranspose_eq_inv u hmul hunit g⁻¹, inv_inv,
        ← doubledRep_conjTranspose_eq_inv u hmul hunit g]
    calc (∑ g : G, hsInner X ((doubledRep u g)ᴴ * Y * doubledRep u g))
        = ∑ g : G, hsInner X (doubledRep u g⁻¹ * Y * (doubledRep u g⁻¹)ᴴ) :=
          (Finset.sum_congr rfl fun g _ => (hF g).symm)
      _ = ∑ g : G, hsInner X (doubledRep u g * Y * (doubledRep u g)ᴴ) :=
          Equiv.sum_comp (Equiv.inv G)
            (fun g => hsInner X (doubledRep u g * Y * (doubledRep u g)ᴴ))
  simp only [twirl2, repTwirl, hsInner_smul_left, hsInner_sum_left, hsInner_smul_right,
    hsInner_sum_right]
  rw [starRingEnd_apply, star_inv₀, star_natCast,
    Finset.sum_congr rfl (fun g _ => hpg0 (doubledRep u g)), hreidx]

/-- **The doubled twirl fixes the Casimir** when the gate group commutes with it. Note `hCfix` (a
finite-group commutation) is genuinely distinct from the proved Lie-kernel fact
`casimir_mem_adCommutantGG`; it is a named input, not redundant. -/
theorem twirl2_fix_casimir (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hunit : ∀ a, (u a)ᴴ * u a = 1)
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (hCfix : ∀ g, (u g ⊗ₖ u g) * b.casimir = b.casimir * (u g ⊗ₖ u g)) :
    twirl2 u b.casimir = b.casimir := by
  haveI : Nonempty G := ⟨1⟩
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hterm : ∀ g : G, doubledRep u g * b.casimir * (doubledRep u g)ᴴ = b.casimir := by
    intro g
    have hc : doubledRep u g * b.casimir = b.casimir * doubledRep u g := hCfix g
    rw [hc, Matrix.mul_assoc, doubledRep_unit' u hunit, Matrix.mul_one]
  rw [twirl2, repTwirl, Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **`proj_orth` from the genuine twirl.** The residual of `O ⊗ O` against the Casimir equals that
of its twirl — by self-adjointness moved onto the Casimir, which the twirl fixes. -/
theorem twirl2_proj_orth (u : G → Matrix (Fin N) (Fin N) ℂ)
    (hmul : ∀ a b, u (a * b) = u a * u b) (hunit : ∀ a, (u a)ᴴ * u a = 1)
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (hCfix : ∀ g, (u g ⊗ₖ u g) * b.casimir = b.casimir * (u g ⊗ₖ u g))
    (O : Matrix (Fin N) (Fin N) ℂ) :
    hsInner b.casimir (O ⊗ₖ O) = hsInner b.casimir (twirl2 u (O ⊗ₖ O)) := by
  rw [← twirl2_hsInner_selfAdjoint u hmul hunit b.casimir (O ⊗ₖ O),
    twirl2_fix_casimir u hunit b hCfix]

/-! ### The genuine-twirl second-moment witness -/

/-- **`RagoneSecondMoment` from a genuine `t = 2` twirl.** Given a finite gate
group acting through a
unitary representation `u`, the second moment is the genuine doubled twirl `twirl₂ u (O ⊗ₖ O)` — NOT
a hand-set `κ • C` as in `consistencyWitness`. The `var_eq` and `proj_orth` fields are discharged
**from the twirl mechanism** (reality of `⟪ρ⊗ρ, M²(O⊗O)⟫` and `twirl₂`-self-adjointness + Casimir
fixing). The remaining inputs are honest named hypotheses, strictly more granular than positing the
whole second moment:
* `hCfix` — the gate group commutes with the Casimir (so the twirl fixes it);
* `hbridge` — **commutant completeness**: anything commuting with the whole doubled gate group lies
  in the Lie-algebra commutant `adCommutantGG`. (This is the genuine `2`-design content; commutants
  are inclusion-*reversing*, so it is not the naive exp-correspondence.) The twirl supplies the
  premise via `twirl2_commute`;
* `hcarrier` — the twirl lands in the `g ⊗ g` carrier;
* `hSchur` — the deferred Schur one-dimensionality `(g⊗g)^g = span{C}` (H2), as
  in `RagoneInterface`.

`mem_invariant` is therefore **posited** (via `hbridge` + `hcarrier`), not twirl-derived; the twirl
alone only gives membership in the *finite-group* commutant. -/
noncomputable def RagoneSecondMoment.ofTwoDesign
    {gens : Set (Matrix (Fin N) (Fin N) ℂ)} (b : DLAHermBasis gens)
    (u : G → Matrix (Fin N) (Fin N) ℂ) (hmul : ∀ a b, u (a * b) = u a * u b)
    (hunit : ∀ a, (u a)ᴴ * u a = 1) {ρ O : Matrix (Fin N) (Fin N) ℂ}
    (hρ : ρᴴ = ρ) (hO : Oᴴ = O)
    (hSchur : gTensorGInvariant b = Submodule.span ℂ {b.casimir})
    (hCfix : ∀ g, (u g ⊗ₖ u g) * b.casimir = b.casimir * (u g ⊗ₖ u g))
    (hbridge : ∀ M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ,
      (∀ V, (u V ⊗ₖ u V) * M = M * (u V ⊗ₖ u V)) → M ∈ adCommutantGG b)
    (hcarrier : twirl2 u (O ⊗ₖ O) ∈ gTensorG b) :
    RagoneSecondMoment b ρ O where
  variance := (hsInner (ρ ⊗ₖ ρ) (twirl2 u (O ⊗ₖ O))).re
  secondMoment := twirl2 u (O ⊗ₖ O)
  var_eq := by
    have hρρ : (ρ ⊗ₖ ρ)ᴴ = ρ ⊗ₖ ρ := by rw [conjTranspose_kronecker, hρ]
    have hOO : (O ⊗ₖ O)ᴴ = O ⊗ₖ O := by rw [conjTranspose_kronecker, hO]
    have hTw : (twirl2 u (O ⊗ₖ O))ᴴ = twirl2 u (O ⊗ₖ O) := twirl2_isHermitian_of u hOO
    have hreal : (starRingEnd ℂ) (hsInner (ρ ⊗ₖ ρ) (twirl2 u (O ⊗ₖ O)))
        = hsInner (ρ ⊗ₖ ρ) (twirl2 u (O ⊗ₖ O)) := by
      rw [hsInner, starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hρρ, hTw, Matrix.trace_mul_comm]
    exact Complex.conj_eq_iff_re.mp hreal
  mem_invariant := by
    rw [gTensorGInvariant]
    exact Submodule.mem_inf.mpr
      ⟨hbridge _ (fun V => twirl2_commute u hmul hunit (O ⊗ₖ O) V), hcarrier⟩
  invariant_eq_spanC := hSchur
  proj_orth := twirl2_proj_orth u hmul hunit b hCfix O

/-! ### Non-vacuity: the genuine-twirl witness is inhabited (trivial group)

The trivial gate group `PUnit` realizes `twirl₂` as the identity, so `ofTwoDesign`'s hypothesis
bundle is genuinely satisfiable. This is an inhabitation check only: on `Fin 1` the twirl equals the
identity and `O ⊗ O = C`, so it does **not** exhibit the honesty differential over
`consistencyWitness`
(that `twirl₂(O⊗O) ≠ κ·C`), which needs a `≥ 2`-dimensional concrete `2`-design (deferred). -/

/-- The trivial (`Unit`) gate group makes the doubled twirl the identity. -/
theorem twirl2_trivial (X : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    twirl2 (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ)) X = X := by
  rw [twirl2, repTwirl]
  simp [doubledRep, Matrix.conjTranspose_one]

/-- **The genuine `ofTwoDesign` witness is inhabited.** Its hypothesis bundle is satisfiable
(witnessed by the trivial `Unit` gate group on the trivial DLA), so the genuine-twirl variance
witness is non-vacuous. -/
theorem ragone_ofTwoDesign_nonempty :
    Nonempty (RagoneSecondMoment trivialDLAHermBasis
      (1 : Matrix (Fin 1) (Fin 1) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  have hcas : twirl2 (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      ((1 : Matrix (Fin 1) (Fin 1) ℂ) ⊗ₖ 1) = trivialDLAHermBasis.casimir := by
    rw [twirl2_trivial, DLAHermBasis.casimir]
    simp [trivialDLAHermBasis]
  refine ⟨RagoneSecondMoment.ofTwoDesign trivialDLAHermBasis (fun _ : Unit => 1)
    (fun _ _ => (one_mul 1).symm) (fun _ => by rw [conjTranspose_one, one_mul])
    conjTranspose_one conjTranspose_one trivialDLA_invariant_eq_spanC
    (fun _ => by simp only [Matrix.one_kronecker_one, Matrix.one_mul, Matrix.mul_one]) ?_ ?_⟩
  · -- hbridge: on the trivial DLA every M lies in adCommutantGG (the doubled action of B = 1 is 0)
    intro M _
    rw [adCommutantGG, Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker,
      show trivialDLAHermBasis.B j = (1 : Matrix (Fin 1) (Fin 1) ℂ) from rfl]
    simp only [doubledAd, Matrix.one_kronecker_one, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one]
    abel
  · -- hcarrier: twirl₂(1⊗1) = C ∈ g ⊗ g
    rw [hcas]
    exact casimir_mem_gTensorG _

end QuantumAlg
