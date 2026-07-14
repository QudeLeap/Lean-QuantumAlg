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
public import QuantumAlg.Primitives.QNN.Algebras.SymplecticDLA

/-!
# The Schur identity `(g⊗g)^g = span{C}` for `sp(2ⁿ)`

Discharges the Schur one-dimensionality hypothesis (H2) for the symplectic algebra `sp(2ⁿ)` — the
`θ=+1` Pauli strings — by feeding the symplectic Pauli structure (`PauliAlgebra`) into the generic
structure-constant solver (`SchurGeneric`), exactly as `PauliStringSchur` does for `su(2ⁿ)`. The
adjoint matrix is a single-term signed permutation, its square is diagonal with a symplectic
eigenvalue, and the anticommutation graph *restricted to the symplectic strings* is
connected — so the
coefficient matrix of any invariant tensor is a scalar, i.e. `(g⊗g)^g = span{C}`.

The reusable machine (the `SchurGeneric` solver and the `PauliAlgebra`
brackets/`ω`/phase) is generic
and shared verbatim with `su`; what is genuinely new here is that the separation and connectivity
witnesses must stay **inside** the symplectic string set `{s : spSign s = 1}` (the `su` witnesses —
single-site Paulis and `pauliXor a b` — can escape it). The set is closed under `pauliXor` of an
anticommuting symplectic pair (`spSign_xor_of_anticomm`), which is what the adjoint support needs.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

/-! ### The multiplicative behaviour of `spSign` under `pauliXor` -/

/-- `yConjSign` is a homomorphism for the Klein-four product: `ε(a⊕b) = ε(a)·ε(b)`
(`ε(a) = (-1)^{x_a ⊕ z_a}`). -/
theorem yConjSign_xor (a b : Fin 4) : yConjSign (xor4 a b) = yConjSign a * yConjSign b := by
  fin_cases a <;> fin_cases b <;> simp [yConjSign, xor4]

/-- The `Y`-parity sign twists by the symplectic form under the Klein-four product:
`ySign(a⊕b) = ySign(a)·ySign(b)·(−1)^{ω(a,b)}`. -/
theorem ySign_xor (a b : Fin 4) :
    ySign (xor4 a b) = ySign a * ySign b * negOnePow (omega4 a b) := by
  fin_cases a <;> fin_cases b <;> simp [ySign, xor4, omega4, negOnePow]

/-- The transpose parity of a product string twists by the total symplectic form:
`∏ₖ ySign((a⊕b)ₖ) = (∏ₖ ySign aₖ)(∏ₖ ySign bₖ)·(−1)^{ω(a,b)}`. -/
theorem prod_ySign_xor (a b : Fin n → Fin 4) :
    (∏ k, ySign (pauliXor a b k))
      = (∏ k, ySign (a k)) * (∏ k, ySign (b k)) * negOnePow (pauliOmega a b) := by
  have hpt : ∀ k, ySign (pauliXor a b k)
      = ySign (a k) * ySign (b k) * negOnePow (omega4 (a k) (b k)) :=
    fun k => by rw [pauliXor]; exact ySign_xor (a k) (b k)
  rw [Finset.prod_congr rfl (fun k _ => hpt k), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    negOnePow_sum, pauliOmega]

/-- **The symplectic sign under the Klein-four product**:
`spSign(a⊕b) = − spSign(a)·spSign(b)·(−1)^{ω(a,b)}`. The lone `−1` is the qubit-`0` twist of `θ`. -/
theorem spSign_xor [NeZero n] (a b : Fin n → Fin 4) :
    spSign (pauliXor a b) = - spSign a * spSign b * negOnePow (pauliOmega a b) := by
  simp only [spSign, ← prod_ySign_eq]
  have h0 : pauliXor a b 0 = xor4 (a 0) (b 0) := rfl
  rw [h0, yConjSign_xor, prod_ySign_xor]
  ring

/-- `spSign` of the identity string is `−1` (the identity is not symplectic). -/
theorem spSign_zero [NeZero n] : spSign (0 : Fin n → Fin 4) = -1 := by
  have hy : (∏ k, ySign ((0 : Fin n → Fin 4) k)) = 1 :=
    Finset.prod_eq_one fun k _ => by simp [ySign]
  rw [spSign, ← prod_ySign_eq, hy]
  simp [yConjSign]

/-- **The symplectic set is closed under the product of an anticommuting symplectic pair.** This is
the in-set closure the adjoint support needs (`su`'s full-nonzero closure does not restrict
here). -/
theorem spSign_xor_of_anticomm [NeZero n] {a b : Fin n → Fin 4}
    (ha : spSign a = 1) (hb : spSign b = 1) (hω : pauliOmega a b = 1) :
    spSign (pauliXor a b) = 1 := by
  rw [spSign_xor, ha, hb, hω, negOnePow_one]; ring

/-! ### Small-support witness plumbing -/

/-- The single-site symplectic pairing: `ω(σ_r^g, d) = ω₄(g, d_r)`. -/
theorem pauliOmega_update_single_left (r : Fin n) (g : Fin 4) (d : Fin n → Fin 4) :
    pauliOmega (Function.update (0 : Fin n → Fin 4) r g) d = omega4 g (d r) := by
  rw [pauliOmega, Finset.sum_eq_single r]
  · rw [Function.update_self]
  · intro k _ hk; rw [Function.update_of_ne hk, Pi.zero_apply, omega4_zero_left]
  · intro h; exact absurd (Finset.mem_univ r) h

/-- The `#Y` count of a single-site Pauli: `1` iff the site carries `Y`. -/
theorem yCount_update_single (r : Fin n) (g : Fin 4) :
    yCount (Function.update (0 : Fin n → Fin 4) r g) = if g = 2 then 1 else 0 := by
  rw [yCount]
  by_cases hg : g = 2
  · rw [if_pos hg]
    have hset : (Finset.univ.filter fun k => Function.update (0 : Fin n → Fin 4) r g k = 2)
        = {r} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hk
        by_contra hne
        rw [Function.update_of_ne hne, Pi.zero_apply] at hk
        exact absurd hk (by decide)
      · intro hk; subst hk; rw [Function.update_self]; exact hg
    rw [hset, Finset.card_singleton]
  · rw [if_neg hg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    by_cases hk : k = r
    · subst hk; rw [Function.update_self]; exact hg
    · rw [Function.update_of_ne hk, Pi.zero_apply]; decide

/-- The zeroth entry of a single-site Pauli. -/
theorem update_single_apply_zero [NeZero n] (r : Fin n) (g : Fin 4) :
    Function.update (0 : Fin n → Fin 4) r g 0 = if r = 0 then g else 0 := by
  by_cases hr : r = 0
  · subst hr; rw [Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne (Ne.symm hr), Pi.zero_apply, if_neg hr]

/-- `spSign` of a single-site Pauli in closed form. -/
theorem spSign_update_single [NeZero n] (r : Fin n) (g : Fin 4) :
    spSign (Function.update (0 : Fin n → Fin 4) r g)
      = -((-1 : ℂ) ^ (if g = 2 then 1 else 0) * yConjSign (if r = 0 then g else 0)) := by
  rw [spSign, yCount_update_single, update_single_apply_zero]

/-- `X₀`, `Y₀`, `Z₀` are symplectic (any non-identity single Pauli on qubit `0`). -/
theorem spSign_update_zero [NeZero n] {g : Fin 4} (hg : g ≠ 0) :
    spSign (Function.update (0 : Fin n → Fin 4) 0 g) = 1 := by
  rw [spSign_update_single, if_pos rfl]
  fin_cases g
  · exact absurd rfl hg
  all_goals simp [yConjSign]

/-- A single `Y` off qubit `0` is symplectic. -/
theorem spSign_update_offzero_Y [NeZero n] {r : Fin n} (hr : r ≠ 0) :
    spSign (Function.update (0 : Fin n → Fin 4) r 2) = 1 := by
  rw [spSign_update_single, if_neg hr, if_pos rfl]
  simp [yConjSign]

/-- A single `X` or `Z` off qubit `0` is **not** symplectic (`spSign = -1`). -/
theorem spSign_update_offzero_XZ [NeZero n] {r : Fin n} (hr : r ≠ 0) {g : Fin 4}
    (hg : g = 1 ∨ g = 3) : spSign (Function.update (0 : Fin n → Fin 4) r g) = -1 := by
  rw [spSign_update_single, if_neg hr]
  rcases hg with h | h <;> subst h <;> simp [yConjSign]

/-! ### In-set separation: every nonzero string anticommutes with a symplectic string -/

/-- **In-set non-degeneracy.** Every nonzero Pauli string anticommutes with some *symplectic* string
(the `su` witness — a single-site Pauli — can fail to be symplectic, so an explicit
`θ=+1` witness is
built by cases on the support of `d`). -/
theorem exists_sp_anticomm [NeZero n] {d : Fin n → Fin 4} (hd : d ≠ 0) :
    ∃ k, spSign k = 1 ∧ pauliOmega k d = 1 := by
  by_cases hA : ∃ q : Fin n, q ≠ 0 ∧ d q ≠ 0
  · obtain ⟨q, hq0, hdq⟩ := hA
    by_cases hY : d q = 2
    · -- A2: `d q = Y`; witness `p₀` on qubit 0 (commuting with `d₀`, fixing the sign) times `Z_q`
      refine ⟨pauliXor (Function.update 0 (0 : Fin n) (if d 0 = 0 then 1 else d 0))
        (Function.update 0 q 3), ?_, ?_⟩
      · have hp0ne : (if d 0 = 0 then 1 else d 0) ≠ 0 := by
          split
          · decide
          · rename_i h; exact h
        have hb0 : Function.update (0 : Fin n → Fin 4) q 3 0 = 0 := by
          rw [update_single_apply_zero, if_neg hq0]
        have hab : pauliOmega (Function.update 0 (0 : Fin n) (if d 0 = 0 then 1 else d 0))
            (Function.update 0 q 3) = 0 := by
          rw [pauliOmega_update_single_left, hb0, omega4_comm, omega4_zero_left]
        rw [spSign_xor, spSign_update_zero hp0ne, spSign_update_offzero_XZ hq0 (Or.inr rfl), hab,
          negOnePow_zero]
        ring
      · have hp0comm : omega4 (if d 0 = 0 then 1 else d 0) (d 0) = 0 := by
          split
          · rename_i h; rw [h]; decide
          · exact omega4_self_zero (d 0)
        rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left,
          hp0comm, hY]
        decide
    · -- A1: `d q ∈ {X,Z}`; witness `Y_q`
      refine ⟨Function.update 0 q 2, spSign_update_offzero_Y hq0, ?_⟩
      rw [pauliOmega_update_single_left]
      have hcases : d q = 1 ∨ d q = 3 := by
        rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (d q) with
          h | h | h | h
        · exact absurd h hdq
        · exact Or.inl h
        · exact absurd h hY
        · exact Or.inr h
      rcases hcases with h | h <;> rw [h] <;> decide
  · -- B: the only nonzero site is qubit 0; witness a single anticommuting Pauli there
    have hA' : ∀ q : Fin n, q ≠ 0 → d q = 0 := fun q hq0 => by
      by_contra hdq; exact hA ⟨q, hq0, hdq⟩
    have hd0 : d 0 ≠ 0 := by
      intro h0; apply hd; funext k
      rcases eq_or_ne k 0 with hk | hk
      · rw [hk, h0]; rfl
      · rw [hA' k hk]; rfl
    refine ⟨Function.update 0 (0 : Fin n) (if d 0 = 1 then 2 else 1), spSign_update_zero (by
      split <;> decide), ?_⟩
    rw [pauliOmega_update_single_left]
    rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (d 0) with
      h | h | h | h
    · exact absurd h hd0
    all_goals rw [h]; decide

/-! ### In-set connectivity: the symplectic anticommutation graph is connected -/

/-- The symplectic anchor `Y₀` is a symplectic string. -/
theorem spSign_siteY0 [NeZero n] : spSign (siteY0 n) = 1 := by
  rw [siteY0]; exact spSign_update_zero (by decide)

/-- The anchor `Y₀` entrywise: `Y` on qubit `0`, identity elsewhere. -/
theorem siteY0_apply [NeZero n] (k : Fin n) : siteY0 n k = if k = 0 then 2 else 0 := by
  rw [siteY0]
  by_cases hk : k = 0
  · rw [hk, Function.update_self, if_pos rfl]
  · rw [Function.update_of_ne hk, if_neg hk]

/-- The pairing of any string with the anchor `Y₀` sees only qubit `0`: `ω(x, Y₀) = ω₄(x₀, Y)`. -/
theorem pauliOmega_siteY0 [NeZero n] (x : Fin n → Fin 4) :
    pauliOmega x (siteY0 n) = omega4 (x 0) 2 := by
  rw [pauliOmega, Finset.sum_eq_single 0
    (fun k _ hk => by rw [siteY0_apply, if_neg hk, omega4_comm, omega4_zero_left])
    (fun h => absurd (Finset.mem_univ 0) h), siteY0_apply, if_pos rfl]

/-- **In-set connectivity (constancy form).** Any function `T` constant across anticommuting
*symplectic* strings is constant on all symplectic strings — because every symplectic string is at
symplectic-anticommutation distance `≤ 2` from the fixed anchor `Y₀`. -/
theorem spAnticomm_const [NeZero n] {α : Type*} {T : (Fin n → Fin 4) → α}
    (hT : ∀ a b, spSign a = 1 → spSign b = 1 → pauliOmega a b = 1 → T a = T b)
    {x : Fin n → Fin 4} (hx : spSign x = 1) : T x = T (siteY0 n) := by
  by_cases hxa : pauliOmega x (siteY0 n) = 1
  · exact hT x (siteY0 n) hx spSign_siteY0 hxa
  · have hx0 : x 0 = 0 ∨ x 0 = 2 := by
      rw [pauliOmega_siteY0] at hxa
      rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (x 0) with
        h | h | h | h
      · exact Or.inl h
      · exact absurd (by rw [h]; decide : omega4 (x 0) 2 = 1) hxa
      · exact Or.inr h
      · exact absurd (by rw [h]; decide : omega4 (x 0) 2 = 1) hxa
    rcases hx0 with hxI | hxY
    · -- `x₀ = I`: `x` has a nonzero site `q ≠ 0`; common neighbour `w = X₀ · h_q`
      have hxne : x ≠ 0 := fun h0 => by rw [h0, spSign_zero] at hx; exact absurd hx (by norm_num)
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hxne
      have hxq : x q ≠ 0 := by simpa using hq
      have hq0 : q ≠ 0 := fun h => by rw [h, hxI] at hxq; exact hxq rfl
      have hhXZ :
          (if x q = 3 then (1 : Fin 4) else 3) = 1 ∨
            (if x q = 3 then (1 : Fin 4) else 3) = 3 := by
        split <;> [exact Or.inl rfl; exact Or.inr rfl]
      have hhanti : omega4 (if x q = 3 then (1 : Fin 4) else 3) (x q) = 1 := by
        rcases (show ∀ z : Fin 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 from by decide) (x q) with
          h | h | h | h
        · exact absurd h hxq
        · rw [h]; decide
        · rw [h]; decide
        · rw [h]; decide
      have hwsp : spSign (pauliXor (Function.update 0 (0 : Fin n) 1)
          (Function.update 0 q (if x q = 3 then (1 : Fin 4) else 3))) = 1 := by
        have hb0 :
            Function.update (0 : Fin n → Fin 4) q
                (if x q = 3 then (1 : Fin 4) else 3) 0 = 0 := by
          rw [update_single_apply_zero, if_neg hq0]
        rw [spSign_xor, spSign_update_zero (by decide), spSign_update_offzero_XZ hq0 hhXZ,
          pauliOmega_update_single_left, hb0, omega4_comm, omega4_zero_left, negOnePow_zero]
        ring
      have hwx : pauliOmega (pauliXor (Function.update 0 (0 : Fin n) 1)
          (Function.update 0 q (if x q = 3 then (1 : Fin 4) else 3))) x = 1 := by
        rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left,
          hxI, hhanti]
        decide
      have hwY : pauliOmega (pauliXor (Function.update 0 (0 : Fin n) 1)
          (Function.update 0 q (if x q = 3 then (1 : Fin 4) else 3))) (siteY0 n) = 1 := by
        rw [pauliOmega_xor_left, pauliOmega_update_single_left, pauliOmega_update_single_left,
          siteY0_apply, siteY0_apply, if_pos rfl, if_neg hq0, omega4_comm _ (0 : Fin 4),
          omega4_zero_left]
        decide
      have e1 : T x = T _ := hT x _ hx hwsp (by rw [pauliOmega_comm]; exact hwx)
      have e2 : T (siteY0 n) = T _ := hT (siteY0 n) _ spSign_siteY0 hwsp (by
        rw [pauliOmega_comm]; exact hwY)
      rw [e1, e2]
    · -- `x₀ = Y`: common neighbour `w = X₀`
      have hwsp : spSign (Function.update (0 : Fin n → Fin 4) 0 1) = 1 :=
        spSign_update_zero (by decide)
      have hwx : pauliOmega (Function.update (0 : Fin n → Fin 4) 0 1) x = 1 := by
        rw [pauliOmega_update_single_left, hxY]; decide
      have hwY : pauliOmega (Function.update (0 : Fin n → Fin 4) 0 1) (siteY0 n) = 1 := by
        rw [pauliOmega_update_single_left, siteY0_apply, if_pos rfl]
        decide
      have e1 : T x = T _ := hT x _ hx hwsp (by rw [pauliOmega_comm]; exact hwx)
      have e2 : T (siteY0 n) = T _ := hT (siteY0 n) _ spSign_siteY0 hwsp (by
        rw [pauliOmega_comm]; exact hwY)
      rw [e1, e2]

/-! ### The `sp(2ⁿ)` Schur family -/

/-- **The `sp(2ⁿ)` family as a `PauliSchurFamily`.** The family strings are exactly the
`θ = +1` labels enumerated by `spEquiv`; the bespoke inputs are the symplectic in-set closure,
separation witness, and anchor-`Y₀` connectivity proved above. -/
noncomputable def spSchurFamily (n : ℕ) [NeZero n] : PauliSchurFamily n (spHermBasis n) where
  mem s := spSign s = 1
  equiv := spEquiv n
  B_eq _ := rfl
  not_mem_zero := by
    intro h
    rw [spSign_zero] at h
    exact absurd h (by norm_num)
  xor_closed := by
    intro a c ha hc hω
    exact spSign_xor_of_anticomm ha hc hω
  sep_witness := by
    intro a c _ _ hac
    have hd : pauliXor a c ≠ 0 := fun he => hac (by
      have hh := pauliXor_self_inv a c
      rw [he, pauliXor_zero_right] at hh
      exact hh)
    exact exists_sp_anticomm hd
  conn_const := by
    intro T h x y hx hy
    exact (spAnticomm_const h hx).trans (spAnticomm_const h hy).symm

/-! ### The Schur identity for `sp(2ⁿ)` -/

/-- **The Schur identity `(g⊗g)^g = span{C}` for `sp(2ⁿ)`** (all `n ≥ 1`).
Discharges the Schur hypothesis (H2) for the symplectic algebra: the hard inclusion
`(g⊗g)^g ≤ span{C}` is genuinely proved
from the symplectic Pauli structure, with `gTensorGInvariant` the genuine
`adCommutantGG ⊓ gTensorG`.
[RBS+23] -/
theorem spHermBasis_schur (n : ℕ) [NeZero n] :
    gTensorGInvariant (spHermBasis n) = Submodule.span ℂ {(spHermBasis n).casimir} :=
  (spSchurFamily n).schur

/-- **Schur-discharged consistency witness for `sp(2ⁿ)`.** With the Schur identity (H2) discharged
by `spHermBasis_schur`, the diagonal witness sequence has exponentially vanishing variance. The
second moment is still `RagoneSecondMoment.consistencyWitness`, not a finite-group global symplectic
twirl. [MBS+18, maintext.tex:148] -/
theorem spN_hasBarrenPlateau_schurDischarged :
    HasBarrenPlateau (fun n => (spSM n (spHermBasis_schur (n + 1))).variance) :=
  spN_hasBarrenPlateau (M := fun n => spSM n (spHermBasis_schur (n + 1)))
    (fun n => (spHermBasis (n + 1)).herm (spI0 n))
    (fun n => (spHermBasis (n + 1)).herm (spI0 n))
    (C := 1) zero_le_one (by
      intro n
      simp [DLAHermBasis.gPurity_basis_elem])

end QuantumAlg
