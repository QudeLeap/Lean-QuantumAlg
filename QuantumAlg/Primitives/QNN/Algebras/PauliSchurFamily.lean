/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliAlgebra
public import QuantumAlg.Primitives.QNN.Interface.SchurGeneric

/-!
# The Pauli-family Schur-discharge solver

Every Pauli-string dynamical Lie algebra treated in this development — the full traceless
family, the symplectic family, the orthogonal family — discharges the Schur one-dimensionality
`(g⊗g)^g = span{C}` by the same argument on top of `SchurGeneric`: the adjoint matrix is a
single-term signed permutation supported on the string product, its square is diagonal with a
symplectic eigenvalue that vanishes exactly on commuting strings, the eigenvalues separate
distinct basis indices, and the in-set anticommutation graph is connected. What is genuinely
bespoke per family is only the underlying string set and four facts about it.

`PauliSchurFamily` bundles exactly those bespoke inputs: the string predicate with its basis
enumeration and normalized-Pauli basis shape, closure of the set under the product of an
anticommuting pair, an in-set separation witness, and in-set connectivity of the
anticommutation graph. Everything else — the closed-form adjoint matrix, the diagonal square,
the eigenvalue/commutation dichotomy, separation and connectivity at the index level, and the
final Schur identity `PauliSchurFamily.schur` — is derived here once, family-independently.
-/

@[expose] public section

namespace QuantumAlg

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The diagonal eigenvalue of the squared adjoint matrix (family-independent; a
`PauliSchurFamily` proves the square IS diagonal with these entries). -/
noncomputable def adMu {N : ℕ} {gens : Set (Matrix (Fin N) (Fin N) ℂ)}
    (b : DLAHermBasis gens) (k a : Fin b.dim) : ℂ :=
  (adMatrix b k * adMatrix b k) a a

/-! ### The bespoke per-family inputs -/

/-- **The bespoke inputs of a Pauli-string Schur discharge.** A family is a set of `n`-qubit
Pauli-string labels (`mem`), enumerated by the basis indices (`equiv`) and realized as the
normalized Pauli matrices (`B_eq`), together with the four facts the structure-constant solver
needs: the identity is outside the set, the set is closed under the product of an anticommuting
pair, every distinct pair of family strings is separated by an in-set witness, and the in-set
anticommutation graph is connected. Producing these is the per-family work; the Schur identity
`PauliSchurFamily.schur` then follows family-independently. -/
structure PauliSchurFamily (n : ℕ) {gens : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)}
    (b : DLAHermBasis gens) where
  /-- The family's string set. -/
  mem : (Fin n → Fin 4) → Prop
  /-- The basis indices enumerate exactly the family's strings. -/
  equiv : Fin b.dim ≃ {s : Fin n → Fin 4 // mem s}
  /-- Each basis element is the normalized Pauli matrix of its label. -/
  B_eq : ∀ i, b.B i = rtNinv n • pauliMat (equiv i).1
  /-- The identity string is not in the family. -/
  not_mem_zero : ¬ mem 0
  /-- The family is closed under the product of an anticommuting pair. -/
  xor_closed : ∀ {a c : Fin n → Fin 4}, mem a → mem c → pauliOmega a c = 1 →
    mem (pauliXor a c)
  /-- In-set separation: the XOR of two distinct family strings anticommutes with some family
  string. This is the exact hypothesis used to separate the squared-adjoint eigenvalues. -/
  sep_witness : ∀ {a c : Fin n → Fin 4}, mem a → mem c → a ≠ c →
    ∃ s, mem s ∧ pauliOmega s (pauliXor a c) = 1
  /-- In-set connectivity: a function constant across anticommuting family pairs is constant
  on the family. -/
  conn_const : ∀ (T : (Fin n → Fin 4) → ℂ),
    (∀ a c, mem a → mem c → pauliOmega a c = 1 → T a = T c) →
    ∀ {x y : Fin n → Fin 4}, mem x → mem y → T x = T y

namespace PauliSchurFamily

variable {n : ℕ} {gens : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)} {b : DLAHermBasis gens}

/-! ### Labels -/

/-- The Pauli-string label of the `i`-th basis element. -/
noncomputable def str (F : PauliSchurFamily n b) (i : Fin b.dim) : Fin n → Fin 4 :=
  (F.equiv i).1

theorem str_mem (F : PauliSchurFamily n b) (i : Fin b.dim) : F.mem (F.str i) := (F.equiv i).2

theorem str_injective (F : PauliSchurFamily n b) {a a' : Fin b.dim}
    (h : F.str a = F.str a') : a = a' :=
  F.equiv.injective (Subtype.ext h)

/-- Family labels are nonzero (the identity is not in the family). -/
theorem str_ne (F : PauliSchurFamily n b) (i : Fin b.dim) : F.str i ≠ 0 := fun h =>
  F.not_mem_zero (h ▸ F.str_mem i)

theorem str_symm_apply (F : PauliSchurFamily n b) {s : Fin n → Fin 4} (hs : F.mem s) :
    F.str (F.equiv.symm ⟨s, hs⟩) = s := by
  rw [str, Equiv.apply_symm_apply]

/-! ### The adjoint matrix in closed form -/

/-- **The family adjoint matrix in closed form.** `(Sₖ)_{a,i} = ⟪Bₐ, ⁅Bₖ, Bᵢ⁆⟫` is a single
symplectic term: nonzero only when `σₐ = σₖ ⊕ σᵢ`, with the commutator phase coefficient. -/
theorem adMatrix_apply (F : PauliSchurFamily n b) (k a i : Fin b.dim) :
    adMatrix b k a i
      = rtNinv n * rtNinv n * rtNinv n *
          (pauliPhase (F.str k) (F.str i) - pauliPhase (F.str i) (F.str k)) *
          (if F.str a = pauliXor (F.str k) (F.str i) then (2 ^ n : ℂ) else 0) := by
  rw [adMatrix, Matrix.of_apply, F.B_eq a, F.B_eq k, F.B_eq i, smul_lie, lie_smul,
    pauliMat_bracket_closed, hsInner_smul_left, hsInner_smul_right, hsInner_smul_right,
    hsInner_smul_right, starRingEnd_apply, rtNinv_conj, pauliMat_hsInner]
  simp only [str]
  ring_nf

/-- Support of the adjoint matrix: it vanishes unless `σₐ = σₖ ⊕ σᵢ`. -/
theorem adMatrix_eq_zero (F : PauliSchurFamily n b) {k a i : Fin b.dim}
    (h : F.str a ≠ pauliXor (F.str k) (F.str i)) : adMatrix b k a i = 0 := by
  rw [F.adMatrix_apply, if_neg h, mul_zero]

/-- Non-vanishing of the adjoint matrix when the support condition holds and the strings
anticommute. -/
theorem adMatrix_ne_zero (F : PauliSchurFamily n b) {k a i : Fin b.dim}
    (hsupp : F.str a = pauliXor (F.str k) (F.str i))
    (hanti : pauliOmega (F.str k) (F.str i) = 1) : adMatrix b k a i ≠ 0 := by
  rw [F.adMatrix_apply, if_pos hsupp]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · exact rtNinv_ne_zero n
  · exact rtNinv_ne_zero n
  · exact rtNinv_ne_zero n
  · exact pauliPhase_sub_ne_zero hanti
  · exact pow_ne_zero n (by norm_num)

/-- Vanishing when the two strings commute (the commutator coefficient is zero). -/
theorem adMatrix_eq_zero_of_comm (F : PauliSchurFamily n b) {k a i : Fin b.dim}
    (h : pauliOmega (F.str k) (F.str i) = 0) : adMatrix b k a i = 0 := by
  rw [F.adMatrix_apply, pauliPhase_sub_eq_zero h, mul_zero, zero_mul]

/-! ### The square is diagonal, with a separating symplectic eigenvalue -/

/-- **The square of the adjoint matrix is diagonal** (the single-term Pauli structure). -/
theorem adMatrix_sq_diagonal (F : PauliSchurFamily n b) (k : Fin b.dim) :
    adMatrix b k * adMatrix b k = Matrix.diagonal (adMu b k) := by
  ext a a'
  rw [Matrix.diagonal_apply]
  by_cases ha : a = a'
  · subst ha; rw [if_pos rfl, adMu]
  · rw [if_neg ha, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : F.str a = pauliXor (F.str k) (F.str i)
    · have h2 : F.str i ≠ pauliXor (F.str k) (F.str a') := fun hi =>
        ha (F.str_injective (by rw [h1, hi, pauliXor_self_inv]))
      rw [F.adMatrix_eq_zero h2, mul_zero]
    · rw [F.adMatrix_eq_zero h1, zero_mul]

/-- **The eigenvalue is zero iff the strings commute.** -/
theorem mu_eq_zero_iff (F : PauliSchurFamily n b) (k a : Fin b.dim) :
    adMu b k a = 0 ↔ pauliOmega (F.str k) (F.str a) = 0 := by
  constructor
  · intro h
    by_contra hω
    have hω1 : pauliOmega (F.str k) (F.str a) = 1 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
        (pauliOmega (F.str k) (F.str a)) with h0 | h1
      · exact absurd h0 hω
      · exact h1
    have hmem : F.mem (pauliXor (F.str k) (F.str a)) :=
      F.xor_closed (F.str_mem k) (F.str_mem a) hω1
    set i₀ := F.equiv.symm ⟨pauliXor (F.str k) (F.str a), hmem⟩ with hi₀
    have hσi₀ : F.str i₀ = pauliXor (F.str k) (F.str a) := F.str_symm_apply hmem
    have hsupp : F.str a = pauliXor (F.str k) (F.str i₀) := by
      rw [hσi₀, pauliXor_self_inv]
    have hanti : pauliOmega (F.str k) (F.str i₀) = 1 := by
      rw [hσi₀, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, hω1]
    have hμ : adMu b k a = adMatrix b k a i₀ * adMatrix b k i₀ a := by
      rw [adMu, Matrix.mul_apply]
      refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
      by_cases h1 : F.str a = pauliXor (F.str k) (F.str i)
      · refine absurd (F.str_injective ?_) hi
        have hii : F.str i = pauliXor (F.str k) (F.str a) := by
          have hsi := pauliXor_self_inv (F.str k) (F.str i)
          rw [← h1] at hsi
          exact hsi.symm
        exact hii.trans hσi₀.symm
      · rw [F.adMatrix_eq_zero h1, zero_mul]
    rw [hμ] at h
    rcases mul_eq_zero.mp h with hz | hz
    · exact F.adMatrix_ne_zero hsupp hanti hz
    · exact F.adMatrix_ne_zero hσi₀ hω1 hz
  · intro h
    rw [adMu, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : F.str a = pauliXor (F.str k) (F.str i)
    · have hi0 : F.str i = pauliXor (F.str k) (F.str a) := by
        have hsi := pauliXor_self_inv (F.str k) (F.str i)
        rw [← h1] at hsi
        exact hsi.symm
      have hcomm : pauliOmega (F.str k) (F.str i) = 0 := by
        rw [hi0, pauliOmega_xor_right, pauliOmega_self_zero, zero_add, h]
      rw [F.adMatrix_eq_zero_of_comm hcomm, zero_mul]
    · rw [F.adMatrix_eq_zero h1, zero_mul]

/-- **Separation**: for distinct indices, some `k` gives distinct eigenvalues. The witness is
the family's in-set separation string, so it indexes a genuine basis element. -/
theorem mu_sep (F : PauliSchurFamily n b) {a a' : Fin b.dim} (ha : a ≠ a') :
    ∃ k, adMu b k a ≠ adMu b k a' := by
  have hstr : F.str a ≠ F.str a' := fun h => ha (F.str_injective h)
  obtain ⟨s, hssp, hs⟩ := F.sep_witness (F.str_mem a) (F.str_mem a') hstr
  refine ⟨F.equiv.symm ⟨s, hssp⟩, ?_⟩
  have hσk : F.str (F.equiv.symm ⟨s, hssp⟩) = s := F.str_symm_apply hssp
  rw [pauliOmega_xor_right] at hs
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (pauliOmega s (F.str a)) with hx | hx
  · have hy : pauliOmega s (F.str a') = 1 := by rw [hx, zero_add] at hs; exact hs
    have hka : adMu b (F.equiv.symm ⟨s, hssp⟩) a = 0 :=
      (F.mu_eq_zero_iff _ a).mpr (by rw [hσk]; exact hx)
    have hka' : adMu b (F.equiv.symm ⟨s, hssp⟩) a' ≠ 0 :=
      (F.mu_eq_zero_iff _ a').not.mpr (by rw [hσk, hy]; exact one_ne_zero)
    rw [hka]; exact Ne.symm hka'
  · have hy : pauliOmega s (F.str a') = 0 := by
      rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (pauliOmega s (F.str a'))
        with h0 | h1
      · exact h0
      · rw [hx, h1] at hs; exact absurd hs (by decide)
    have hka : adMu b (F.equiv.symm ⟨s, hssp⟩) a ≠ 0 :=
      (F.mu_eq_zero_iff _ a).not.mpr (by rw [hσk, hx]; exact one_ne_zero)
    have hka' : adMu b (F.equiv.symm ⟨s, hssp⟩) a' = 0 :=
      (F.mu_eq_zero_iff _ a').mpr (by rw [hσk]; exact hy)
    rw [hka']; exact hka

/-! ### Index-level connectivity -/

/-- **The adjoint-support graph on the family is connected**, lifted from the family's
string-level connectivity through the enumeration. -/
theorem conn (F : PauliSchurFamily n b) (t : Fin b.dim → ℂ)
    (ht : ∀ x y : Fin b.dim, (∃ k, adMatrix b k x y ≠ 0) → t x = t y)
    (x y : Fin b.dim) : t x = t y := by
  classical
  set T : (Fin n → Fin 4) → ℂ :=
    fun s => if hs : F.mem s then t (F.equiv.symm ⟨s, hs⟩) else 0 with hT
  have hTval : ∀ z : Fin b.dim, T (F.str z) = t z := by
    intro z
    rw [hT]
    simp only [dif_pos (F.str_mem z)]
    congr 1
    have he : (⟨F.str z, F.str_mem z⟩ : {s : Fin n → Fin 4 // F.mem s}) = F.equiv z :=
      Subtype.ext rfl
    rw [he, Equiv.symm_apply_apply]
  have hedge : ∀ a c : Fin n → Fin 4, F.mem a → F.mem c → pauliOmega a c = 1 → T a = T c := by
    intro a c hsa hsc hac
    have hmem : F.mem (pauliXor a c) := F.xor_closed hsa hsc hac
    have hTa : T a = t (F.equiv.symm ⟨a, hsa⟩) := by
      have hva := hTval (F.equiv.symm ⟨a, hsa⟩); rwa [F.str_symm_apply hsa] at hva
    have hTc : T c = t (F.equiv.symm ⟨c, hsc⟩) := by
      have hvc := hTval (F.equiv.symm ⟨c, hsc⟩); rwa [F.str_symm_apply hsc] at hvc
    rw [hTa, hTc]
    refine ht _ _ ⟨F.equiv.symm ⟨pauliXor a c, hmem⟩, ?_⟩
    refine F.adMatrix_ne_zero ?_ ?_
    · rw [F.str_symm_apply hsa, F.str_symm_apply hmem, F.str_symm_apply hsc,
        pauliXor_xor_self_right]
    · rw [F.str_symm_apply hmem, F.str_symm_apply hsc, pauliOmega_xor_left,
        pauliOmega_self_zero, add_zero, hac]
  have hres := F.conn_const T hedge (F.str_mem x) (F.str_mem y)
  rw [hTval, hTval] at hres
  exact hres

/-! ### The Schur identity -/

/-- **The family Schur identity `(g⊗g)^g = span{C}`**, derived once from the bespoke inputs:
the hard inclusion feeds the closed-form adjoint machinery into the generic structure-constant
solver, the easy inclusion is `spanC_le_gTensorGInvariant`. -/
theorem schur (F : PauliSchurFamily n b) :
    gTensorGInvariant b = Submodule.span ℂ {b.casimir} := by
  refine le_antisymm (fun X hX => ?_) (spanC_le_gTensorGInvariant _)
  have hoff : ∀ a a' : Fin b.dim, a ≠ a' → coeffMatrix b X a a' = 0 :=
    fun a a' ha => coeffMatrix_offdiag_zero b hX (adMu b) F.adMatrix_sq_diagonal
      (fun a a' h => F.mu_sep h) ha
  exact gTensorGInvariant_le_spanC b hX hoff (coeffMatrix_diag_const b hX hoff F.conn)

end PauliSchurFamily

end QuantumAlg
