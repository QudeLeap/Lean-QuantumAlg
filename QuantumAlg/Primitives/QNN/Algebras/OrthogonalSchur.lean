/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Interface.SchurGeneric
public import QuantumAlg.Primitives.QNN.Algebras.PauliSchurFamily
public import QuantumAlg.Primitives.QNN.Algebras.OrthogonalDLA

/-!
# The Schur identity `(g⊗g)^g = span{C}` for the simple `so(2ⁿ)`

Discharges the Schur one-dimensionality hypothesis (H2) for the orthogonal algebra `so(2ⁿ)` — the
odd-`#Y` Pauli strings — by feeding the symplectic Pauli structure (`PauliAlgebra`) into the generic
structure-constant solver (`SchurGeneric`), as `PauliStringSchur` does for `su(2ⁿ)`.

**Simple members only.** The odd-`#Y` anticommutation graph is connected for every `m ≠ 2`, but at
`m = 2` (i.e. `so(4)`) it splits into two triangles `{IY,YX,YZ}` and `{XY,YI,ZY}` — reflecting
`so(4) ≅ su(2) ⊕ su(2)`, for which `(g⊗g)^g` is genuinely **two**-dimensional and `= span{C}` is
FALSE. So the Schur identity here is stated for `m ≠ 2`; the reductive `so(4)` case is treated
separately via the two-Casimir `RagoneReductive` framework, and `so(2) = soHermBasis 1` is the
degenerate dim-1 abelian special case.

The reusable machine (the `SchurGeneric` solver and the `PauliAlgebra`
brackets/`ω`/phase) is generic
and shared verbatim; the in-set separation and connectivity witnesses must stay inside the odd-`#Y`
string set (the `su` witnesses can escape it). The set is closed under `pauliXor` of an
anticommuting
odd-`#Y` pair (`soMem_xor_of_anticomm`), which is what the adjoint support needs.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {m : ℕ}

/-! ### The `#Y`-parity behaviour under `pauliXor` -/

private theorem ySign_xor (a b : Fin 4) :
    ySign (xor4 a b) = ySign a * ySign b * negOnePow (omega4 a b) := by
  fin_cases a <;> fin_cases b <;> simp [ySign, xor4, omega4, negOnePow]

private theorem prod_ySign_xor (a b : Fin m → Fin 4) :
    (∏ k, ySign (pauliXor a b k))
      = (∏ k, ySign (a k)) * (∏ k, ySign (b k)) * negOnePow (pauliOmega a b) := by
  have hpt : ∀ k, ySign (pauliXor a b k)
      = ySign (a k) * ySign (b k) * negOnePow (omega4 (a k) (b k)) :=
    fun k => by rw [pauliXor]; exact ySign_xor (a k) (b k)
  rw [Finset.prod_congr rfl (fun k _ => hpt k), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    negOnePow_sum, pauliOmega]

/-- **The odd-`#Y` set is closed under the product of an anticommuting odd-`#Y` pair.** -/
theorem soMem_xor_of_anticomm {a b : Fin m → Fin 4}
    (ha : Odd (yCount a)) (hb : Odd (yCount b)) (hω : pauliOmega a b = 1) :
    Odd (yCount (pauliXor a b)) := by
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have h1 : (-1 : ℂ) ^ yCount (pauliXor a b) = 1 := hne.neg_one_pow
  have h2 : (-1 : ℂ) ^ yCount (pauliXor a b) = -1 := by
    rw [← prod_ySign_eq, prod_ySign_xor, prod_ySign_eq, prod_ySign_eq, ha.neg_one_pow,
      hb.neg_one_pow, hω, negOnePow_one]
    ring
  rw [h1] at h2
  exact absurd h2 (by norm_num)

/-! ### Small-support witness plumbing (private; the generic versions live in `SymplecticSchur`) -/

/-- The single-site symplectic pairing: `ω(σ_r^g, d) = ω₄(g, d_r)`. -/
private theorem pauliOmega_update_single_left (r : Fin m) (g : Fin 4) (d : Fin m → Fin 4) :
    pauliOmega (Function.update (0 : Fin m → Fin 4) r g) d = omega4 g (d r) := by
  rw [pauliOmega, Finset.sum_eq_single r]
  · rw [Function.update_self]
  · intro k _ hk; rw [Function.update_of_ne hk, Pi.zero_apply, omega4_zero_left]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- A string that is `Y` at exactly one site (and non-`Y` elsewhere) has `#Y = 1`. -/
private theorem yCount_eq_one {z : Fin m → Fin 4} {s : Fin m} (hs : z s = 2)
    (hne : ∀ k, k ≠ s → z k ≠ 2) : yCount z = 1 := by
  rw [yCount]
  have hset : (Finset.univ.filter fun k => z k = 2) = {s} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => by_contra fun hks => hne k hks hk, fun hk => hk ▸ hs⟩
  rw [hset, Finset.card_singleton]

/-- Reading off a two-site witness `σ_q^g ⊕ σ_r^h` (`q ≠ r`) at an index. -/
private theorem xor2_apply {q r : Fin m} (hqr : q ≠ r) (g h : Fin 4) (k : Fin m) :
    pauliXor (Function.update 0 q g) (Function.update 0 r h) k
      = if k = q then g else if k = r then h else 0 := by
  simp only [pauliXor]
  by_cases hq : k = q
  · subst hq
    rw [Function.update_self, Function.update_of_ne hqr, Pi.zero_apply, if_pos rfl,
      show xor4 g 0 = g from by fin_cases g <;> rfl]
  · rw [Function.update_of_ne hq, Pi.zero_apply, if_neg hq]
    by_cases hr : k = r
    · subst hr; rw [Function.update_self, if_pos rfl, show xor4 0 h = h from by fin_cases h <;> rfl]
    · rw [Function.update_of_ne hr, Pi.zero_apply, if_neg hr]; decide

/-- Reading off a three-site witness `σ_0^{g₀} ⊕ σ_p^{gₚ} ⊕ σ_r^{gᵣ}` at an index
(`0,p,r` distinct). -/
private theorem xor3_apply [NeZero m] {p r : Fin m} (h0p : (0 : Fin m) ≠ p) (h0r : (0 : Fin m) ≠ r)
    (hpr : p ≠ r) (g0 gp gr : Fin 4) (k : Fin m) :
    pauliXor (pauliXor (Function.update 0 0 g0) (Function.update 0 p gp))
        (Function.update 0 r gr) k
      = if k = 0 then g0 else if k = p then gp else if k = r then gr else 0 := by
  simp only [pauliXor, Function.update_apply, Pi.zero_apply]
  split_ifs with h1 h2 h3 <;>
    first
      | (fin_cases g0 <;> rfl)
      | (fin_cases gp <;> rfl)
      | (fin_cases gr <;> rfl)
      | decide
      | simp_all

/-- With at least three qubits, any two sites miss a third. -/
private theorem exists_third_site (hm : 3 ≤ m) (a b : Fin m) : ∃ r, r ≠ a ∧ r ≠ b := by
  have h2 : ({a, b} : Finset (Fin m)).card ≤ 2 := (Finset.card_insert_le a {b}).trans (by simp)
  have hne : ({a, b} : Finset (Fin m)) ≠ Finset.univ := by
    intro he; rw [he, Finset.card_univ, Fintype.card_fin] at h2; omega
  obtain ⟨r, _, hr⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  rw [Finset.mem_insert, Finset.mem_singleton] at hr
  exact ⟨r, fun h => hr (Or.inl h), fun h => hr (Or.inr h)⟩

/-- The odd-`#Y` anchor `Y₀`. -/
private theorem pauliOmega_soAnchor [NeZero m] (x : Fin m → Fin 4) :
    pauliOmega x (Function.update (0 : Fin m → Fin 4) 0 2) = omega4 (x 0) 2 := by
  rw [pauliOmega, Finset.sum_eq_single 0
    (fun k _ hk => by rw [Function.update_of_ne hk, Pi.zero_apply, omega4_comm, omega4_zero_left])
    (fun h => absurd (Finset.mem_univ 0) h), Function.update_self]

private theorem odd_yCount_soAnchor [NeZero m] :
    Odd (yCount (Function.update (0 : Fin m → Fin 4) 0 2)) := by
  rw [yCount_eq_one (s := 0) (Function.update_self ..)
    (fun k hk => by rw [Function.update_of_ne hk, Pi.zero_apply]; decide)]
  decide

/-! ### In-set separation and connectivity (simple members `m ≥ 3`) -/

/-- **In-set non-degeneracy** (`m ≥ 2`). Every nonzero string anticommutes with some
odd-`#Y` string.
(The lone exception is the trivial `so(2)`, `m = 1`, whose only string `Y` commutes with itself.) -/
theorem exists_so_anticomm {d : Fin m → Fin 4} (hm : 2 ≤ m) (hd : d ≠ 0) :
    ∃ k, Odd (yCount k) ∧ pauliOmega k d = 1 := by
  by_cases hXZ : ∃ q, d q = 1 ∨ d q = 3
  · -- a support site carries `X`/`Z`: a single `Y` there
    obtain ⟨q, hq⟩ := hXZ
    refine ⟨Function.update 0 q 2, ?_, ?_⟩
    · rw [yCount_eq_one (s := q) (Function.update_self ..)
        (fun k hk => by rw [Function.update_of_ne hk, Pi.zero_apply]; decide)]
      decide
    · rw [pauliOmega_update_single_left]
      rcases hq with h | h <;> rw [h] <;> decide
  · -- support is pure `Y`: `X` at a `Y`-site, `Y` at a distinct site
    have hd0 : ∃ q, d q = 2 := by
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hd
      have hq0 : d q ≠ 0 := by simpa using hq
      refine ⟨q, ?_⟩
      rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (d q) with
        h | h | h | h
      · exact absurd h hq0
      · exact absurd ⟨q, Or.inl h⟩ hXZ
      · exact h
      · exact absurd ⟨q, Or.inr h⟩ hXZ
    obtain ⟨q, hq⟩ := hd0
    haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    obtain ⟨r, hr⟩ := exists_ne q
    refine ⟨pauliXor (Function.update 0 q 1) (Function.update 0 r 2), ?_, ?_⟩
    · rw [yCount_eq_one (s := r) (by rw [xor2_apply (Ne.symm hr), if_neg hr, if_pos rfl])
        (fun k hk => by
          rw [xor2_apply (Ne.symm hr)]
          by_cases hkq : k = q
          · rw [if_pos hkq]; decide
          · rw [if_neg hkq, if_neg hk]; decide)]
      decide
    · rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left, hq]
      have hdr : omega4 2 (d r) = 0 := by
        rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (d r) with
          h | h | h | h
        · rw [h]; decide
        · exact absurd ⟨r, Or.inl h⟩ hXZ
        · rw [h]; decide
        · exact absurd ⟨r, Or.inr h⟩ hXZ
      rw [hdr]; decide

/-- **Common anchor-neighbour** (`m ≥ 3`). Any odd-`#Y` string that commutes with the anchor `Y₀`
(`x₀ ∈ {I, Y}`) has an odd-`#Y` string anticommuting with both it and `Y₀`. The three-qubit lower
bound is genuine: `so(4)` (`m = 2`) has only one spare site and is disconnected. -/
private theorem exists_so_common (hm : 3 ≤ m) [NeZero m] {x : Fin m → Fin 4}
    (hx : Odd (yCount x)) (hx0 : x 0 = 0 ∨ x 0 = 2) :
    ∃ z, Odd (yCount z) ∧ pauliOmega z x = 1 ∧
      pauliOmega z (Function.update (0 : Fin m → Fin 4) 0 2) = 1 := by
  have ha0 : ∀ z : Fin m → Fin 4, z 0 = 1 →
      pauliOmega z (Function.update (0 : Fin m → Fin 4) 0 2) = 1 :=
    fun z hz => by rw [pauliOmega_soAnchor, hz]; decide
  -- a distinguished `Y`-site of `x`
  have hYsite : ∃ p, x p = 2 := by
    have hpos : 0 < yCount x := hx.pos
    rw [yCount, Finset.card_pos] at hpos
    obtain ⟨p, hp⟩ := hpos
    exact ⟨p, (Finset.mem_filter.mp hp).2⟩
  rcases hx0 with hI | hY
  · -- x₀ = I
    by_cases hq : ∃ q, q ≠ 0 ∧ (x q = 1 ∨ x q = 3)
    · -- A-gen: z = X₀ · Y_q
      obtain ⟨q, hq0, hqXZ⟩ := hq
      refine ⟨pauliXor (Function.update 0 0 1) (Function.update 0 q 2), ?_, ?_,
        ha0 _ (by rw [xor2_apply (Ne.symm hq0), if_pos rfl])⟩
      · rw [yCount_eq_one (s := q) (by rw [xor2_apply (Ne.symm hq0), if_neg hq0, if_pos rfl])
          (fun k hk => by
            rw [xor2_apply (Ne.symm hq0)]
            by_cases hk0 : k = 0
            · rw [if_pos hk0]; decide
            · rw [if_neg hk0, if_neg hk]; decide)]
        decide
      · rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left, hI]
        rcases hqXZ with h | h <;> rw [h] <;> decide
    · -- A-hard: all sites ≥1 are I/Y; z = X₀ · X_p · Y_r
      obtain ⟨p, hp⟩ := hYsite
      have hp0 : p ≠ 0 := fun h => by rw [h, hI] at hp; exact absurd hp (by decide)
      obtain ⟨r, hr0, hrp⟩ := exists_third_site hm 0 p
      have hxr : x r = 0 ∨ x r = 2 := by
        rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (x r) with
          h | h | h | h
        · exact Or.inl h
        · exact absurd ⟨r, hr0, Or.inl h⟩ hq
        · exact Or.inr h
        · exact absurd ⟨r, hr0, Or.inr h⟩ hq
      refine ⟨pauliXor (pauliXor (Function.update 0 0 1) (Function.update 0 p 1))
        (Function.update 0 r 2), ?_, ?_,
        ha0 _ (by rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp), if_pos rfl])⟩
      · rw [yCount_eq_one (s := r)
          (by rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp), if_neg hr0, if_neg hrp,
            if_pos rfl])
          (fun k hk => by
            rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp)]
            by_cases hk0 : k = 0
            · rw [if_pos hk0]; decide
            · rw [if_neg hk0]; by_cases hkp : k = p
              · rw [if_pos hkp]; decide
              · rw [if_neg hkp, if_neg hk]; decide)]
        decide
      · rw [pauliOmega_xor_left, pauliOmega_xor_left, pauliOmega_update_single_left,
          pauliOmega_update_single_left, pauliOmega_update_single_left, hI, hp]
        rcases hxr with h | h <;> rw [h] <;> decide
  · -- x₀ = Y
    by_cases hq : ∃ q, q ≠ 0 ∧ (x q = 0 ∨ x q = 2)
    · -- B-gen: z = X₀ · Y_q
      obtain ⟨q, hq0, hqIY⟩ := hq
      refine ⟨pauliXor (Function.update 0 0 1) (Function.update 0 q 2), ?_, ?_,
        ha0 _ (by rw [xor2_apply (Ne.symm hq0), if_pos rfl])⟩
      · rw [yCount_eq_one (s := q) (by rw [xor2_apply (Ne.symm hq0), if_neg hq0, if_pos rfl])
          (fun k hk => by
            rw [xor2_apply (Ne.symm hq0)]
            by_cases hk0 : k = 0
            · rw [if_pos hk0]; decide
            · rw [if_neg hk0, if_neg hk]; decide)]
        decide
      · rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left, hY]
        rcases hqIY with h | h <;> rw [h] <;> decide
    · -- B-hard: all sites ≥1 are X/Z; z = X₀ · Y_p · c_r
      have hall : ∀ q, q ≠ 0 → x q = 1 ∨ x q = 3 := by
        intro q hq0
        rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (x q) with
          h | h | h | h
        · exact absurd ⟨q, hq0, Or.inl h⟩ hq
        · exact Or.inl h
        · exact absurd ⟨q, hq0, Or.inr h⟩ hq
        · exact Or.inr h
      have hp0 : (⟨1, by omega⟩ : Fin m) ≠ 0 := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; omega
      obtain ⟨r, hr0, hrp⟩ := exists_third_site hm 0 ⟨1, by omega⟩
      have hxp := hall ⟨1, by omega⟩ hp0
      have hxr := hall r hr0
      refine ⟨pauliXor (pauliXor (Function.update 0 0 1) (Function.update 0 ⟨1, by omega⟩ 2))
        (Function.update 0 r (if x r = 1 then 3 else 1)), ?_, ?_,
        ha0 _ (by rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp), if_pos rfl])⟩
      · rw [yCount_eq_one (s := (⟨1, by omega⟩ : Fin m))
          (by rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp), if_neg hp0, if_pos rfl])
          (fun k hk => by
            rw [xor3_apply (Ne.symm hp0) (Ne.symm hr0) (Ne.symm hrp)]
            by_cases hk0 : k = 0
            · rw [if_pos hk0]; decide
            · rw [if_neg hk0]; by_cases hkp : k = ⟨1, by omega⟩
              · exact absurd hkp hk
              · rw [if_neg hkp]; by_cases hkr : k = r
                · rw [if_pos hkr]; split <;> decide
                · rw [if_neg hkr]; decide)]
        decide
      · rw [pauliOmega_xor_left, pauliOmega_xor_left, pauliOmega_update_single_left,
          pauliOmega_update_single_left, pauliOmega_update_single_left, hY]
        rcases hxp with h | h <;> rw [h] <;>
          (rcases hxr with h' | h' <;> rw [h'] <;> decide)

/-- **In-set connectivity (constancy form), simple members `m ≥ 3`.** -/
theorem soAnticomm_const [NeZero m] (hm : 3 ≤ m) {α : Type*} {T : (Fin m → Fin 4) → α}
    (hT : ∀ a b, Odd (yCount a) → Odd (yCount b) → pauliOmega a b = 1 → T a = T b)
    {x : Fin m → Fin 4} (hx : Odd (yCount x)) :
    T x = T (Function.update (0 : Fin m → Fin 4) 0 2) := by
  by_cases hxa : pauliOmega x (Function.update (0 : Fin m → Fin 4) 0 2) = 1
  · exact hT x _ hx odd_yCount_soAnchor hxa
  · have hx0 : x 0 = 0 ∨ x 0 = 2 := by
      rw [pauliOmega_soAnchor] at hxa
      rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (x 0) with
        h | h | h | h
      · exact Or.inl h
      · exact absurd (by rw [h]; decide : omega4 (x 0) 2 = 1) hxa
      · exact Or.inr h
      · exact absurd (by rw [h]; decide : omega4 (x 0) 2 = 1) hxa
    obtain ⟨z, hzodd, hzx, hza0⟩ := exists_so_common hm hx hx0
    have e1 := hT x z hx hzodd (by rw [pauliOmega_comm]; exact hzx)
    have e2 := hT (Function.update (0 : Fin m → Fin 4) 0 2) z odd_yCount_soAnchor hzodd
      (by rw [pauliOmega_comm]; exact hza0)
    rw [e1, e2]

/-! ### The simple `so(2ᵐ)` Schur family -/

/-- **The simple `so(2ᵐ)` family as a `PauliSchurFamily`.** The family strings are exactly the
odd-`#Y` labels enumerated by `soEquiv`; the bespoke inputs are the odd-`#Y` in-set closure,
separation witness, and anchor-`Y₀` connectivity proved above. The `m ≥ 3` hypothesis excludes the
reductive `so(4)` split case. -/
noncomputable def soSchurFamily (m : ℕ) (hm : 3 ≤ m) : PauliSchurFamily m (soHermBasis m) where
  mem s := Odd (yCount s)
  equiv := soEquiv m
  B_eq _ := rfl
  not_mem_zero := by
    intro h
    have h0 : yCount (0 : Fin m → Fin 4) = 0 := by
      rw [yCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _
      rw [Pi.zero_apply]
      decide
    rw [h0] at h
    exact absurd h (by decide)
  xor_closed := by
    intro a c ha hc hω
    exact soMem_xor_of_anticomm ha hc hω
  sep_witness := by
    intro a c _ _ hac
    have hd : pauliXor a c ≠ 0 := fun he => hac (by
      have hh := pauliXor_self_inv a c
      rw [he, pauliXor_zero_right] at hh
      exact hh)
    exact exists_so_anticomm (by omega : 2 ≤ m) hd
  conn_const := by
    intro T h x y hx hy
    haveI : NeZero m := ⟨by omega⟩
    exact (soAnticomm_const hm h hx).trans (soAnticomm_const hm h hy).symm

/-! ### The Schur identity for the simple `so(2ⁿ)` -/

/-- The one-dimensional `so(2)` member has the Schur identity for the same reason as any
one-dimensional abelian basis: there are no off-diagonal coefficient matrices. This is a separate
low-dimensional case, not part of the simple `m ≥ 3` family. -/
theorem soHermBasis_one_schur :
    gTensorGInvariant (soHermBasis 1) = Submodule.span ℂ {(soHermBasis 1).casimir} := by
  have hdim : (soHermBasis 1).dim = 1 := by
    rw [soHermBasis_dim, soDim]
    decide
  haveI : Subsingleton (Fin (soHermBasis 1).dim) := by rw [hdim]; infer_instance
  refine le_antisymm (fun X hX => ?_) (spanC_le_gTensorGInvariant _)
  exact gTensorGInvariant_le_spanC (soHermBasis 1) hX
    (fun a a' ha => absurd (Subsingleton.elim a a') ha)
    (fun a a' => by rw [Subsingleton.elim a a'])

/-- **The Schur identity `(g⊗g)^g = span{C}` for the simple `so(2ᵐ)`** (`m ≥ 3`).
Discharges the Schur hypothesis (H2) for the orthogonal algebra at the simple members: the
hard inclusion `(g⊗g)^g ≤ span{C}`
is genuinely proved from the odd-`#Y` Pauli structure, with `gTensorGInvariant` the genuine
`adCommutantGG ⊓ gTensorG`. The identity is FALSE at `m = 2` (`so(4) ≅ su(2)⊕su(2)`, commutant is
two-dimensional) and degenerate at `m = 1` (`so(2)`, abelian, dimension one); those two members are
treated as separate special cases. [RBS+23] -/
theorem soHermBasis_schur (m : ℕ) (hm : 3 ≤ m) :
    gTensorGInvariant (soHermBasis m) = Submodule.span ℂ {(soHermBasis m).casimir} :=
  (soSchurFamily m hm).schur

/-- **Schur-discharged consistency witness for the simple `so(2ᵐ)` family.** With the Schur identity
(H2) discharged by `soHermBasis_schur` for `m ≥ 3`, the diagonal witness sequence over
`so(2ⁿ⁺³) = so(8), so(16), …` has exponentially vanishing variance. The second moment is still the
consistency witness, not a finite-group global orthogonal twirl. [MBS+18, maintext.tex:148] -/
theorem soN_hasBarrenPlateau_schurDischarged :
    HasBarrenPlateau (fun n => (soSM (n + 2) (soHermBasis_schur (n + 3) (by omega))).variance) := by
  refine soN_hasBarrenPlateau (M := fun n => soSM (n + 2) (soHermBasis_schur (n + 3) (by omega)))
    (fun n => (soHermBasis (n + 3)).herm (soI0 (n + 2)))
    (fun n => (soHermBasis (n + 3)).herm (soI0 (n + 2)))
    (C := 1) zero_le_one ?_
  intro n
  simp [DLAHermBasis.gPurity_basis_elem]

end QuantumAlg
