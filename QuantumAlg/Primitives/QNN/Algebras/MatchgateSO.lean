/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.PauliSchurFamily
public import QuantumAlg.Primitives.QNN.Algebras.OrthogonalSO4
public import QuantumAlg.Primitives.QNN.Simulation.PolyDLA
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Matchgate/free-fermion `so(2n)` Pauli-Majorana DLA

This module isolates the matchgate/free-fermion polynomial-DLA spine as a Pauli
Majorana-frame construction. A `PauliMajoranaFrame n` is a concrete choice of
`2n` Pauli labels on `n` qubits that pairwise anticommute, i.e. a spin
representation of Majorana generators. The Hermitian quadratic labels are the
unordered-edge XORs `γ_a γ_b`; signs of `i γ_a γ_b` do not affect the Hermitian
Hilbert-Schmidt basis, span, or Schur calculations.

The second-moment statements in this file are consistency witnesses only. They
do not assert a genuine finite matchgate-group twirl.
-/

@[expose] public section

namespace QuantumAlg

open Matrix
open scoped Sym2

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A concrete Pauli realization of `2n` Majorana generators: the labels pairwise anticommute. -/
structure PauliMajoranaFrame (n : ℕ) where
  /-- The `a`-th Majorana generator as an `n`-qubit Pauli label. -/
  v : Fin (2 * n) → (Fin n → Fin 4)
  /-- Distinct Majorana labels pairwise anticommute. -/
  anti : ∀ a b : Fin (2 * n), a ≠ b → pauliOmega (v a) (v b) = 1

/-- The unordered non-diagonal pairs of `2n` Majorana indices. -/
abbrev MatchgateSOEdge (n : ℕ) := (⊤ : SimpleGraph (Fin (2 * n))).edgeSet

/-- The complete-graph edge from two distinct Majorana indices. -/
def matchgateSOEdgeOfNe {n : ℕ} (a b : Fin (2 * n)) (h : a ≠ b) : MatchgateSOEdge n :=
  ⟨s(a, b), by
    rw [SimpleGraph.mem_edgeSet]
    simpa using h⟩

@[simp] theorem matchgateSOEdgeOfNe_val {n : ℕ} (a b : Fin (2 * n)) (h : a ≠ b) :
    (matchgateSOEdgeOfNe a b h : Sym2 (Fin (2 * n))) = s(a, b) := rfl

/-- The number of Majorana-quadratic labels is `binom(2n,2) = n(2n-1)`. -/
theorem matchgateSOEdge_card (n : ℕ) :
    Fintype.card (MatchgateSOEdge n) = n * (2 * n - 1) := by
  change Fintype.card (⊤ : SimpleGraph (Fin (2 * n))).edgeSet = n * (2 * n - 1)
  rw [SimpleGraph.card_edgeSet, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin, Nat.choose_two_right]
  have hmul : 2 * n * (2 * n - 1) = 2 * (n * (2 * n - 1)) := by
    rw [mul_assoc]
  rw [hmul, Nat.mul_div_right _ (by decide : 0 < 2)]

namespace PauliMajoranaFrame

variable {n : ℕ} (F : PauliMajoranaFrame n)

private theorem pauliXor_cancel_left (x y z : Fin n → Fin 4) :
    pauliXor (pauliXor x y) (pauliXor x z) = pauliXor y z := by
  funext k
  simp only [pauliXor]
  generalize hx : x k = xk
  generalize hy : y k = yk
  generalize hz : z k = zk
  fin_cases xk <;> fin_cases yk <;> fin_cases zk <;> rfl

private theorem pauliXor_cancel_right (x y z : Fin n → Fin 4) :
    pauliXor (pauliXor x y) (pauliXor y z) = pauliXor x z := by
  funext k
  simp only [pauliXor]
  generalize hx : x k = xk
  generalize hy : y k = yk
  generalize hz : z k = zk
  fin_cases xk <;> fin_cases yk <;> fin_cases zk <;> rfl

/-- Pairwise Majorana anticommutation in if-then-else form. -/
theorem omega (a b : Fin (2 * n)) :
    pauliOmega (F.v a) (F.v b) = if a = b then 0 else 1 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, pauliOmega_self_zero]
  · rw [if_neg h, F.anti a b h]

/-- The Pauli label of the Hermitian Majorana quadratic indexed by an unordered edge. -/
def edgeLabel (e : Sym2 (Fin (2 * n))) : Fin n → Fin 4 :=
  Sym2.lift ⟨fun a b => pauliXor (F.v a) (F.v b), by
    intro a b
    exact pauliXor_comm (F.v a) (F.v b)⟩ e

@[simp] theorem edgeLabel_mk (a b : Fin (2 * n)) :
    F.edgeLabel s(a, b) = pauliXor (F.v a) (F.v b) := rfl

/-- Non-diagonal Majorana quadratics are non-identity Pauli labels. -/
theorem edgeLabel_ne_zero {e : Sym2 (Fin (2 * n))} (he : ¬ e.IsDiag) :
    F.edgeLabel e ≠ 0 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
      rw [Sym2.mk_isDiag_iff] at he
      intro hz
      have hω : pauliOmega (F.v a) (pauliXor (F.v a) (F.v b)) = 0 := by
        have hcong := congrArg (fun x => pauliOmega (F.v a) x) hz
        rw [edgeLabel_mk] at hcong
        simpa only [Pi.zero_apply] using
          hcong.trans (by rw [pauliOmega_comm (F.v a) 0, pauliOmega_zero_left])
      rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add, F.omega a b, if_neg he] at hω
      exact one_ne_zero hω

/-- The edge-to-quadratic-label map is injective on complete-graph edges. -/
theorem edgeLabel_injective_on_edges :
    Function.Injective (fun e : MatchgateSOEdge n => F.edgeLabel e.1) := by
  intro e₁ e₂ h
  apply Subtype.ext
  cases e₁ with
  | mk z₁ hz₁ =>
  cases e₂ with
  | mk z₂ hz₂ =>
  induction z₁ using Sym2.inductionOn with
  | hf a b =>
  induction z₂ using Sym2.inductionOn with
  | hf c d =>
      simp only [edgeLabel_mk] at h
      have hab : a ≠ b := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₁)
          (by rw [Sym2.mk_isDiag_iff])
      have hcd : c ≠ d := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₂)
          (by rw [Sym2.mk_isDiag_iff])
      have ha_mem : a = c ∨ a = d := by
        by_contra hnot
        push Not at hnot
        have hleft : pauliOmega (F.v a) (pauliXor (F.v a) (F.v b)) = 1 := by
          rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add, F.omega a b, if_neg hab]
        have hright : pauliOmega (F.v a) (pauliXor (F.v c) (F.v d)) = 0 := by
          rw [pauliOmega_xor_right, F.omega a c, F.omega a d, if_neg hnot.1, if_neg hnot.2]
          decide
        rw [h] at hleft
        rw [hright] at hleft
        exact one_ne_zero hleft.symm
      rcases ha_mem with rfl | rfl
      · have hb_eq_d : b = d := by
          have hlabel : F.v b = F.v d := by
            calc
              F.v b = pauliXor (F.v a) (pauliXor (F.v a) (F.v b)) :=
                (pauliXor_self_inv (F.v a) (F.v b)).symm
              _ = pauliXor (F.v a) (pauliXor (F.v a) (F.v d)) := by rw [h]
              _ = F.v d := pauliXor_self_inv (F.v a) (F.v d)
          by_contra hbd
          have hω : pauliOmega (F.v b) (F.v d) = 0 := by
            rw [hlabel, pauliOmega_self_zero]
          rw [F.omega b d, if_neg hbd] at hω
          exact one_ne_zero hω
        subst hb_eq_d
        rfl
      · have hb_eq_c : b = c := by
          have hlabel : F.v b = F.v c := by
            calc
              F.v b = pauliXor (F.v a) (pauliXor (F.v a) (F.v b)) :=
                (pauliXor_self_inv (F.v a) (F.v b)).symm
              _ = pauliXor (F.v a) (pauliXor (F.v c) (F.v a)) := by rw [h]
              _ = pauliXor (F.v a) (pauliXor (F.v a) (F.v c)) := by
                rw [pauliXor_comm (F.v c) (F.v a)]
              _ = F.v c := pauliXor_self_inv (F.v a) (F.v c)
          by_contra hbc
          have hω : pauliOmega (F.v b) (F.v c) = 0 := by
            rw [hlabel, pauliOmega_self_zero]
          rw [F.omega b c, if_neg hbc] at hω
          exact one_ne_zero hω
        subst hb_eq_c
        exact Sym2.eq_swap

/-- Membership in the Majorana-quadratic Pauli-label family. -/
def matchgateSOMem (s : Fin n → Fin 4) : Prop :=
  ∃ e : MatchgateSOEdge n, s = F.edgeLabel e.1

theorem matchgateSOMem_edgeLabel (e : MatchgateSOEdge n) : F.matchgateSOMem (F.edgeLabel e.1) :=
  ⟨e, rfl⟩

/-- The basis-index equivalence with complete-graph Majorana edges. -/
noncomputable def matchgateSOEdgeEquiv :
    Fin (Fintype.card (MatchgateSOEdge n)) ≃ MatchgateSOEdge n :=
  (Fintype.equivFin _).symm

/-- The normalized Hermitian Majorana-quadratic basis element. -/
noncomputable def matchgateSOB (i : Fin (Fintype.card (MatchgateSOEdge n))) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  rtNinv n • pauliMat (F.edgeLabel ((matchgateSOEdgeEquiv (n := n)) i).1)

theorem matchgateSOB_isHermitian (i : Fin (Fintype.card (MatchgateSOEdge n))) :
    (F.matchgateSOB i)ᴴ = F.matchgateSOB i := by
  rw [matchgateSOB, conjTranspose_smul, rtNinv_conj, pauliMat_isHermitian]

theorem matchgateSOB_ortho (i j : Fin (Fintype.card (MatchgateSOEdge n))) :
    hsInner (F.matchgateSOB i) (F.matchgateSOB j) = if i = j then 1 else 0 := by
  rw [matchgateSOB, matchgateSOB, hsInner_smul_left, hsInner_smul_right, starRingEnd_apply,
    rtNinv_conj, ← mul_assoc, rtNinv_mul_self, pauliMat_hsInner]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, one_div,
      inv_mul_cancel₀ (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0))]
  · rw [if_neg h, if_neg ?_, mul_zero]
    intro he
    exact h ((matchgateSOEdgeEquiv (n := n)).injective
      (F.edgeLabel_injective_on_edges he))

theorem edgeLabel_omega_mk (a b c d : Fin (2 * n)) :
    pauliOmega (F.edgeLabel s(a, b)) (F.edgeLabel s(c, d))
      = pauliOmega (F.v a) (F.v c) + pauliOmega (F.v a) (F.v d)
        + (pauliOmega (F.v b) (F.v c) + pauliOmega (F.v b) (F.v d)) := by
  rw [edgeLabel_mk, edgeLabel_mk, pauliOmega_xor_left, pauliOmega_xor_right,
    pauliOmega_xor_right]

/-- Anticommuting Majorana-quadratic labels close under Pauli XOR. -/
theorem matchgateSOMem_xor_of_anticomm {s t : Fin n → Fin 4}
    (hs : F.matchgateSOMem s) (ht : F.matchgateSOMem t) (hω : pauliOmega s t = 1) :
    F.matchgateSOMem (pauliXor s t) := by
  rcases hs with ⟨e₁, rfl⟩
  rcases ht with ⟨e₂, rfl⟩
  cases e₁ with
  | mk z₁ hz₁ =>
  cases e₂ with
  | mk z₂ hz₂ =>
  induction z₁ using Sym2.inductionOn with
  | hf a b =>
  induction z₂ using Sym2.inductionOn with
  | hf c d =>
      have hab : a ≠ b := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₁)
          (by rw [Sym2.mk_isDiag_iff])
      have hcd : c ≠ d := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₂)
          (by rw [Sym2.mk_isDiag_iff])
      by_cases hac : a = c
      · subst hac
        by_cases hbd : b = d
        · subst hbd
          rw [edgeLabel_mk, pauliOmega_self_zero] at hω
          exact absurd hω zero_ne_one
        refine ⟨matchgateSOEdgeOfNe b d hbd, ?_⟩
        simp only [matchgateSOEdgeOfNe_val, edgeLabel_mk]
        exact pauliXor_cancel_left (F.v a) (F.v b) (F.v d)
      · by_cases had : a = d
        · subst had
          by_cases hbc : b = c
          · subst hbc
            rw [edgeLabel_mk, edgeLabel_mk, pauliXor_comm (F.v b) (F.v a),
              pauliOmega_self_zero] at hω
            exact absurd hω zero_ne_one
          refine ⟨matchgateSOEdgeOfNe b c hbc, ?_⟩
          simp only [matchgateSOEdgeOfNe_val, edgeLabel_mk]
          rw [pauliXor_comm (F.v c) (F.v a)]
          exact pauliXor_cancel_left (F.v a) (F.v b) (F.v c)
        · by_cases hbc : b = c
          · subst hbc
            by_cases had' : a = d
            · exact absurd had' had
            refine ⟨matchgateSOEdgeOfNe a d had', ?_⟩
            simp only [matchgateSOEdgeOfNe_val, edgeLabel_mk]
            exact pauliXor_cancel_right (F.v a) (F.v b) (F.v d)
          · by_cases hbd : b = d
            · subst hbd
              refine ⟨matchgateSOEdgeOfNe a c hac, ?_⟩
              simp only [matchgateSOEdgeOfNe_val, edgeLabel_mk]
              rw [pauliXor_comm (F.v c) (F.v b)]
              exact pauliXor_cancel_right (F.v a) (F.v b) (F.v c)
            · have hzero : pauliOmega (F.edgeLabel s(a, b)) (F.edgeLabel s(c, d)) = 0 := by
                rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a d, F.omega b c, F.omega b d,
                  if_neg hac, if_neg had, if_neg hbc, if_neg hbd]
                decide
              rw [hzero] at hω
              exact absurd hω zero_ne_one

private theorem finset_card_four_le {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  calc
    ({a, b, c, d} : Finset α).card ≤ ({b, c, d} : Finset α).card + 1 := by
      simpa using Finset.card_insert_le a ({b, c, d} : Finset α)
    _ ≤ (({c, d} : Finset α).card + 1) + 1 := by
      exact Nat.add_le_add_right
        (by simpa using Finset.card_insert_le b ({c, d} : Finset α)) 1
    _ ≤ ((({d} : Finset α).card + 1) + 1) + 1 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (by simpa using Finset.card_insert_le c ({d} : Finset α)) 1) 1
    _ ≤ 4 := by simp

private theorem exists_fin_ne_four {m : ℕ} (hm : 4 < m) (a b c d : Fin m) :
    ∃ r : Fin m, r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
  classical
  by_contra h
  let S : Finset (Fin m) := {a, b, c, d}
  have hcover : ∀ r : Fin m, r = a ∨ r = b ∨ r = c ∨ r = d := by
    intro r
    by_contra hr
    apply h
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · intro hra; exact hr (Or.inl hra)
    · intro hrb; exact hr (Or.inr (Or.inl hrb))
    · intro hrc; exact hr (Or.inr (Or.inr (Or.inl hrc)))
    · intro hrd; exact hr (Or.inr (Or.inr (Or.inr hrd)))
  have huniv_subset : (Finset.univ : Finset (Fin m)) ⊆ S := by
    intro r _
    rcases hcover r with hr | hr | hr | hr <;> simp [S, hr]
  have hcard_univ_le : m ≤ S.card := by
    simpa [S] using Finset.card_le_card huniv_subset
  have hS_le : S.card ≤ 4 := by
    dsimp [S]
    exact finset_card_four_le a b c d
  omega

theorem edgeLabel_omega_shared_left {a b c : Fin (2 * n)}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    pauliOmega (F.edgeLabel s(a, b)) (F.edgeLabel s(a, c)) = 1 := by
  rw [F.edgeLabel_omega_mk, F.omega a a, F.omega a c, F.omega b a, F.omega b c,
    if_pos rfl, if_neg hac, if_neg (Ne.symm hab), if_neg hbc]
  decide

theorem matchgateSO_conn_const (T : (Fin n → Fin 4) → ℂ)
    (hT : ∀ a c, F.matchgateSOMem a → F.matchgateSOMem c →
      pauliOmega a c = 1 → T a = T c) :
    ∀ {x y : Fin n → Fin 4}, F.matchgateSOMem x → F.matchgateSOMem y → T x = T y := by
  intro x y hx hy
  rcases hx with ⟨e₁, rfl⟩
  rcases hy with ⟨e₂, rfl⟩
  cases e₁ with
  | mk z₁ hz₁ =>
  cases e₂ with
  | mk z₂ hz₂ =>
  induction z₁ using Sym2.inductionOn with
  | hf a b =>
  induction z₂ using Sym2.inductionOn with
  | hf c d =>
      have hab : a ≠ b := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₁)
          (by rw [Sym2.mk_isDiag_iff])
      have hcd : c ≠ d := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₂)
          (by rw [Sym2.mk_isDiag_iff])
      by_cases hac : a = c
      · subst hac
        by_cases hbd : b = d
        · subst hbd
          rfl
        · exact hT _ _
            (F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩)
            (F.matchgateSOMem_edgeLabel ⟨s(a, d), hz₂⟩)
            (F.edgeLabel_omega_shared_left hab hcd hbd)
      · by_cases had : a = d
        · subst had
          by_cases hbc : b = c
          · subst hbc
            rw [edgeLabel_mk, edgeLabel_mk, pauliXor_comm (F.v b) (F.v a)]
          · exact hT _ _
              (F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩)
              (F.matchgateSOMem_edgeLabel ⟨s(c, a), hz₂⟩)
              (by
                rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a a, F.omega b c,
                  F.omega b a, if_neg hac, if_pos rfl, if_neg hbc, if_neg (Ne.symm hab)]
                decide)
        · by_cases hbc : b = c
          · subst hbc
            exact hT _ _
              (F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩)
              (F.matchgateSOMem_edgeLabel ⟨s(b, d), hz₂⟩)
              (by
                rw [F.edgeLabel_omega_mk, F.omega a b, F.omega a d, F.omega b b,
                  F.omega b d, if_neg hab, if_neg had, if_pos rfl, if_neg hcd]
                decide)
          · by_cases hbd : b = d
            · subst hbd
              exact hT _ _
                (F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩)
                (F.matchgateSOMem_edgeLabel ⟨s(c, b), hz₂⟩)
                (by
                  rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a b, F.omega b c,
                    F.omega b b, if_neg hac, if_neg hab, if_neg hbc, if_pos rfl]
                  decide)
            · have hz : F.matchgateSOMem (F.edgeLabel s(a, c)) :=
                F.matchgateSOMem_edgeLabel (matchgateSOEdgeOfNe a c hac)
              have hleft : T (F.edgeLabel s(a, b)) = T (F.edgeLabel s(a, c)) :=
                hT _ _ (F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩) hz
                  (F.edgeLabel_omega_shared_left hab hac hbc)
              have hright : T (F.edgeLabel s(a, c)) = T (F.edgeLabel s(c, d)) :=
                hT _ _ hz (F.matchgateSOMem_edgeLabel ⟨s(c, d), hz₂⟩)
                  (by
                    rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a d, F.omega c c,
                      F.omega c d, if_neg hac, if_neg had, if_pos rfl, if_neg hcd]
                    decide)
              exact hleft.trans hright

theorem matchgateSO_sep_witness (hn : 3 ≤ n) {x y : Fin n → Fin 4}
    (hx : F.matchgateSOMem x) (hy : F.matchgateSOMem y) (hxy : x ≠ y) :
    ∃ s, F.matchgateSOMem s ∧ pauliOmega s (pauliXor x y) = 1 := by
  rcases hx with ⟨e₁, rfl⟩
  rcases hy with ⟨e₂, rfl⟩
  cases e₁ with
  | mk z₁ hz₁ =>
  cases e₂ with
  | mk z₂ hz₂ =>
  induction z₁ using Sym2.inductionOn with
  | hf a b =>
  induction z₂ using Sym2.inductionOn with
  | hf c d =>
      have hab : a ≠ b := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₁)
          (by rw [Sym2.mk_isDiag_iff])
      have hcd : c ≠ d := by
        intro hdiag
        subst hdiag
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz₂)
          (by rw [Sym2.mk_isDiag_iff])
      by_cases hac : a = c
      · subst hac
        by_cases hbd : b = d
        · subst hbd
          exact absurd rfl hxy
        · refine ⟨F.edgeLabel s(a, b), F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩, ?_⟩
          rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add,
            F.edgeLabel_omega_shared_left hab hcd hbd]
      · by_cases had : a = d
        · subst had
          by_cases hbc : b = c
          · subst hbc
            have hlabel : F.edgeLabel s(a, b) = F.edgeLabel s(b, a) := by
              rw [edgeLabel_mk, edgeLabel_mk, pauliXor_comm (F.v b) (F.v a)]
            exact absurd hlabel hxy
          · refine ⟨F.edgeLabel s(a, b), F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩, ?_⟩
            rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add]
            rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a a, F.omega b c,
              F.omega b a, if_neg hac, if_pos rfl, if_neg hbc, if_neg (Ne.symm hab)]
            decide
        · by_cases hbc : b = c
          · subst hbc
            refine ⟨F.edgeLabel s(a, b), F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩, ?_⟩
            rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add]
            rw [F.edgeLabel_omega_mk, F.omega a b, F.omega a d, F.omega b b,
              F.omega b d, if_neg hab, if_neg had, if_pos rfl, if_neg hcd]
            decide
          · by_cases hbd : b = d
            · subst hbd
              refine ⟨F.edgeLabel s(a, b), F.matchgateSOMem_edgeLabel ⟨s(a, b), hz₁⟩, ?_⟩
              rw [pauliOmega_xor_right, pauliOmega_self_zero, zero_add]
              rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a b, F.omega b c,
                F.omega b b, if_neg hac, if_neg hab, if_neg hbc, if_pos rfl]
              decide
            · have hm : 4 < 2 * n := by omega
              obtain ⟨r, hra, hrb, hrc, hrd⟩ := exists_fin_ne_four hm a b c d
              refine ⟨F.edgeLabel s(a, r),
                F.matchgateSOMem_edgeLabel (matchgateSOEdgeOfNe a r (Ne.symm hra)), ?_⟩
              rw [pauliOmega_xor_right]
              have hleft :
                  pauliOmega (F.edgeLabel s(a, r)) (F.edgeLabel s(a, b)) = 1 :=
                F.edgeLabel_omega_shared_left (Ne.symm hra) hab hrb
              have hright :
                  pauliOmega (F.edgeLabel s(a, r)) (F.edgeLabel s(c, d)) = 0 := by
                rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a d, F.omega r c,
                  F.omega r d, if_neg hac, if_neg had, if_neg hrc, if_neg hrd]
                decide
              rw [hleft, hright]
              decide

/-- Equivalence between matchgate edges and their valid Pauli-string labels. -/
noncomputable def matchgateSOStringEquiv :
    MatchgateSOEdge n ≃ {s : Fin n → Fin 4 // F.matchgateSOMem s} :=
  Equiv.ofBijective
    (fun e => ⟨F.edgeLabel e.1, F.matchgateSOMem_edgeLabel e⟩)
    ⟨by
      intro e e' h
      exact F.edgeLabel_injective_on_edges (Subtype.ext_iff.mp h),
     by
      intro s
      rcases s.2 with ⟨e, h⟩
      exact ⟨e, Subtype.ext h.symm⟩⟩

/-- The skew-Hermitian generators of the matchgate `so(2n)` DLA. -/
def matchgateSOGens : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, F.matchgateSOMem s ∧ A = Complex.I • pauliMat s}

/-- Pauli matrices whose labels satisfy the matchgate membership predicate. -/
def matchgateSOPauliSet : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ s : Fin n → Fin 4, F.matchgateSOMem s ∧ A = pauliMat s}

/-- Skew-Hermitian Majorana quadratics attached to the edges of `G`. -/
def graphGens (G : SimpleGraph (Fin (2 * n))) :
    Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {A | ∃ e : G.edgeSet, A = Complex.I • pauliMat (F.edgeLabel e.1)}

theorem pauliMat_mem_matchgateSOPauliSet {s : Fin n → Fin 4} (hs : F.matchgateSOMem s) :
    pauliMat s ∈ F.matchgateSOPauliSet :=
  ⟨s, hs, rfl⟩

theorem matchgateSO_lie_mem_span ⦃x y : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ⦄
    (hx : x ∈ Submodule.span ℂ F.matchgateSOPauliSet)
    (hy : y ∈ Submodule.span ℂ F.matchgateSOPauliSet) :
    ⁅x, y⁆ ∈ Submodule.span ℂ F.matchgateSOPauliSet := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      rcases ha with ⟨sa, hsa, rfl⟩
      rcases hb with ⟨sb, hsb, rfl⟩
      have hcases : pauliOmega sa sb = 0 ∨ pauliOmega sa sb = 1 := by
        exact (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (pauliOmega sa sb)
      rcases hcases with h0 | h1
      · rw [pauliMat_bracket_closed, pauliPhase_sub_eq_zero h0, zero_smul]
        exact Submodule.zero_mem _
      · rw [pauliMat_bracket_closed]
        exact Submodule.smul_mem _ _ (Submodule.subset_span
          (F.pauliMat_mem_matchgateSOPauliSet (F.matchgateSOMem_xor_of_anticomm hsa hsb h1)))
    | zero => rw [lie_zero]; exact Submodule.zero_mem _
    | add b c _ _ hb hc => rw [lie_add]; exact add_mem hb hc
    | smul r b _ hb => rw [lie_smul]; exact Submodule.smul_mem _ _ hb
  | zero => rw [zero_lie]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_lie]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_lie]; exact Submodule.smul_mem _ _ ha

/-- Lie subalgebra spanned by the valid matchgate Pauli matrices. -/
def matchgateSOLie : LieSubalgebra ℂ (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) where
  toSubmodule := Submodule.span ℂ F.matchgateSOPauliSet
  lie_mem' := fun hx hy => F.matchgateSO_lie_mem_span hx hy

theorem matchgateSOGens_subset_matchgateSOLie :
    F.matchgateSOGens ⊆ (F.matchgateSOLie : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
  rintro A ⟨s, hs, rfl⟩
  change Complex.I • pauliMat s ∈ Submodule.span ℂ F.matchgateSOPauliSet
  exact Submodule.smul_mem _ _ (Submodule.subset_span (F.pauliMat_mem_matchgateSOPauliSet hs))

theorem graphGens_subset_matchgateSOLie (G : SimpleGraph (Fin (2 * n))) :
    F.graphGens G ⊆ (F.matchgateSOLie : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) := by
  rintro A ⟨⟨z, hz⟩, rfl⟩
  induction z using Sym2.inductionOn with
  | hf a b =>
      have hab : a ≠ b := (SimpleGraph.mem_edgeSet G).mp hz |>.ne
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        (F.pauliMat_mem_matchgateSOPauliSet
          (F.matchgateSOMem_edgeLabel (matchgateSOEdgeOfNe a b hab))))

private theorem pauliMat_edge_mem_graphDLA_of_adj
    {G : SimpleGraph (Fin (2 * n))} {a b : Fin (2 * n)} (hab : G.Adj a b) :
    pauliMat (F.edgeLabel s(a, b)) ∈ dynamicalLieAlgebra (F.graphGens G) := by
  have hedge : s(a, b) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).mpr hab
  have hgen : Complex.I • pauliMat (F.edgeLabel s(a, b)) ∈
      dynamicalLieAlgebra (F.graphGens G) :=
    generators_subset_dynamicalLieAlgebra (F.graphGens G) ⟨⟨s(a, b), hedge⟩, rfl⟩
  have hpm : pauliMat (F.edgeLabel s(a, b)) =
      (-Complex.I) • (Complex.I • pauliMat (F.edgeLabel s(a, b))) := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  rw [hpm]
  exact Submodule.smul_mem _ _ hgen

private theorem pauliMat_edge_mem_graphDLA_of_isPath
    {G : SimpleGraph (Fin (2 * n))} {a b : Fin (2 * n)}
    (p : G.Walk a b) (hp : p.IsPath) (hab : a ≠ b) :
    pauliMat (F.edgeLabel s(a, b)) ∈ dynamicalLieAlgebra (F.graphGens G) := by
  induction p with
  | nil => exact (hab rfl).elim
  | @cons a c b hac p ih =>
      by_cases hcb : c = b
      · subst hcb
        exact F.pauliMat_edge_mem_graphDLA_of_adj hac
      · have hp' : p.IsPath := hp.of_cons
        have htail := ih hp' hcb
        have hhead := F.pauliMat_edge_mem_graphDLA_of_adj hac
        have hac_ne : a ≠ c := hac.ne
        have hω : pauliOmega (F.edgeLabel s(a, c)) (F.edgeLabel s(c, b)) = 1 := by
          rw [F.edgeLabel_omega_mk, F.omega a c, F.omega a b, F.omega c c,
            F.omega c b, if_neg hac_ne, if_neg hab, if_pos rfl, if_neg hcb]
          decide
        have hbracket : ⁅pauliMat (F.edgeLabel s(a, c)),
            pauliMat (F.edgeLabel s(c, b))⁆ ∈ dynamicalLieAlgebra (F.graphGens G) :=
          LieSubalgebra.lie_mem _ hhead htail
        rw [pauliMat_bracket_closed] at hbracket
        have hxor : pauliXor (F.edgeLabel s(a, c)) (F.edgeLabel s(c, b)) =
            F.edgeLabel s(a, b) := by
          simp only [edgeLabel_mk]
          exact pauliXor_cancel_right (F.v a) (F.v c) (F.v b)
        rw [hxor] at hbracket
        let z := pauliPhase (F.edgeLabel s(a, c)) (F.edgeLabel s(c, b)) -
          pauliPhase (F.edgeLabel s(c, b)) (F.edgeLabel s(a, c))
        have hz : z ≠ 0 := pauliPhase_sub_ne_zero hω
        have hpm : pauliMat (F.edgeLabel s(a, b)) =
            z⁻¹ • (z • pauliMat (F.edgeLabel s(a, b))) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
        rw [hpm]
        exact Submodule.smul_mem _ _ hbracket

/-- A connected Majorana graph generates the full quadratic `so(2n)` span. -/
theorem graph_dla_toSubmodule (G : SimpleGraph (Fin (2 * n))) (hG : G.Connected) :
    (dynamicalLieAlgebra (F.graphGens G)).toSubmodule =
      Submodule.span ℂ F.matchgateSOPauliSet := by
  apply le_antisymm
  · intro x hx
    exact dynamicalLieAlgebra_minimal (F.graphGens G) (F.graphGens_subset_matchgateSOLie G) hx
  · rw [Submodule.span_le]
    intro A hA
    rcases hA with ⟨s, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
    have hne : ¬ z.IsDiag :=
      SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz
    induction z using Sym2.inductionOn with
    | hf a b =>
        rw [Sym2.mk_isDiag_iff] at hne
        obtain ⟨p, hp⟩ := hG.preconnected.exists_isPath a b
        exact F.pauliMat_edge_mem_graphDLA_of_isPath p hp hne

theorem matchgateSO_dla_toSubmodule :
    (dynamicalLieAlgebra F.matchgateSOGens).toSubmodule =
      Submodule.span ℂ F.matchgateSOPauliSet := by
  apply le_antisymm
  · intro x hx
    exact dynamicalLieAlgebra_minimal F.matchgateSOGens F.matchgateSOGens_subset_matchgateSOLie hx
  · rw [Submodule.span_le]
    intro A hA
    rcases hA with ⟨s, hs, rfl⟩
    have hgen : F.matchgateSOGens ⊆ (dynamicalLieAlgebra F.matchgateSOGens : Set _) :=
      generators_subset_dynamicalLieAlgebra F.matchgateSOGens
    have hg : Complex.I • pauliMat s ∈ dynamicalLieAlgebra F.matchgateSOGens :=
      hgen ⟨s, hs, rfl⟩
    have hpm : pauliMat s = (-Complex.I) • (Complex.I • pauliMat s) := by
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    rw [hpm]
    exact Submodule.smul_mem _ _ hg

theorem matchgateSO_range_span :
    Submodule.span ℂ (Set.range F.matchgateSOB) = Submodule.span ℂ F.matchgateSOPauliSet := by
  have hrt : rtNinv n ≠ 0 := rtNinv_ne_zero n
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro i
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (F.pauliMat_mem_matchgateSOPauliSet (F.matchgateSOMem_edgeLabel _)))
  · rw [Submodule.span_le]
    intro A hA
    rcases hA with ⟨s, ⟨e, rfl⟩, rfl⟩
    have hkey : F.matchgateSOB ((matchgateSOEdgeEquiv (n := n)).symm e)
        = rtNinv n • pauliMat (F.edgeLabel e.1) := by
      simp only [matchgateSOB, Equiv.apply_symm_apply]
    have hpm : pauliMat (F.edgeLabel e.1)
        = (rtNinv n)⁻¹ • F.matchgateSOB ((matchgateSOEdgeEquiv (n := n)).symm e) := by
      rw [hkey, smul_smul, inv_mul_cancel₀ hrt, one_smul]
    rw [hpm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The Hermitian orthonormal basis of a connected Majorana graph DLA. -/
noncomputable def graphHermBasis (G : SimpleGraph (Fin (2 * n))) (hG : G.Connected) :
    DLAHermBasis (F.graphGens G) where
  dim := Fintype.card (MatchgateSOEdge n)
  B := F.matchgateSOB
  herm := F.matchgateSOB_isHermitian
  ortho := F.matchgateSOB_ortho
  span_eq := by
    rw [F.matchgateSO_range_span, F.graph_dla_toSubmodule G hG]

/-- The Hermitian orthonormal basis of the Majorana-quadratic matchgate DLA. -/
noncomputable def matchgateSOHermBasis : DLAHermBasis F.matchgateSOGens where
  dim := Fintype.card (MatchgateSOEdge n)
  B := F.matchgateSOB
  herm := F.matchgateSOB_isHermitian
  ortho := F.matchgateSOB_ortho
  span_eq := by
    rw [F.matchgateSO_range_span, F.matchgateSO_dla_toSubmodule]

@[simp] theorem matchgateSOHermBasis_dim :
    F.matchgateSOHermBasis.dim = Fintype.card (MatchgateSOEdge n) := rfl

/-- Closed-form dimension `dim so(2n) = n(2n-1)` for the Majorana-quadratic basis. -/
theorem matchgateSOHermBasis_dim_closedForm :
    F.matchgateSOHermBasis.dim = n * (2 * n - 1) := by
  rw [matchgateSOHermBasis_dim, matchgateSOEdge_card]

/-- Schur-family data built from the matchgate Pauli basis when `3 ≤ n`. -/
noncomputable def matchgateSOSchurFamily (hn : 3 ≤ n) :
    PauliSchurFamily n F.matchgateSOHermBasis where
  mem := F.matchgateSOMem
  equiv := (matchgateSOEdgeEquiv (n := n)).trans F.matchgateSOStringEquiv
  B_eq := by
    intro i
    rfl
  not_mem_zero := by
    rintro ⟨e, h⟩
    have hnd : ¬ e.1.IsDiag :=
      SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) e.2
    exact (F.edgeLabel_ne_zero (e := e.1) hnd) h.symm
  xor_closed := by
    intro a c ha hc hω
    exact F.matchgateSOMem_xor_of_anticomm ha hc hω
  sep_witness := by
    intro a c ha hc hac
    exact F.matchgateSO_sep_witness hn ha hc hac
  conn_const := by
    intro T hT x y hx hy
    exact F.matchgateSO_conn_const T hT hx hy

end PauliMajoranaFrame

/-- Closed-form dimension `dim so(2n) = n(2n-1)` for any Pauli-Majorana matchgate frame. -/
theorem matchgateSOHermBasis_dim_closedForm {n : ℕ} (F : PauliMajoranaFrame n) :
    F.matchgateSOHermBasis.dim = n * (2 * n - 1) :=
  F.matchgateSOHermBasis_dim_closedForm

/-- **Schur identity for the matchgate/free-fermion `so(2n)` family** (`n ≥ 3`). The
`n = 2` member is the reductive `so(4) ≅ su(2) ⊕ su(2)` exception, exposed separately below;
there is intentionally no `n = 1` endpoint. -/
theorem matchgateSOHermBasis_schur {n : ℕ} (F : PauliMajoranaFrame n) (hn : 3 ≤ n) :
    gTensorGInvariant F.matchgateSOHermBasis =
      Submodule.span ℂ {F.matchgateSOHermBasis.casimir} :=
  (F.matchgateSOSchurFamily hn).schur

/-- The `n = 2` matchgate/free-fermion exception is represented by the existing reductive
`so(4)` witness, whose variance splits across the two `su(2)` ideals. -/
theorem matchgateSO4_totalVariance_eq : so4Reductive.variance = 1 / 3 :=
  so4_totalVariance_eq

/-- **Shifted matchgate/free-fermion polynomial-DLA dichotomy.** For any `m ↦ so(2(m+3))`
Pauli-Majorana frame, a reductive consistency witness with an inverse-polynomial distinguished
ideal purity floor rules out a barren plateau and gives exact g-sim reconstruction from
polynomially many matchgate DLA coordinates. This is a consistency witness statement only; it
does not assert a genuine matchgate-group twirl. -/
theorem matchgateSO_polyDLA_family_dichotomy
    (F : (m : ℕ) → PauliMajoranaFrame (m + 3))
    {ρ O : (m : ℕ) → Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ}
    (R : (m : ℕ) → RagoneReductive (ρ m) (O m))
    (hρ : ∀ m, (ρ m)ᴴ = ρ m) (hO : ∀ m, (O m)ᴴ = O m)
    (hdim : ∀ m j, 0 < ((R m).basis j).dim)
    (hOmem : ∀ m, O m ∈ (dynamicalLieAlgebra (F m).matchgateSOGens).toSubmodule)
    (j0 : (m : ℕ) → Fin (R m).numComp)
    {CpIdeal : ℝ} (hCpIdeal : 0 < CpIdeal) {kpIdeal : ℕ}
    (hdim_j0 : ∀ m,
      (((R m).basis (j0 m)).dim : ℝ) ≤ CpIdeal * (((m : ℝ) + 1) ^ kpIdeal))
    {cq : ℝ} (hcq : 0 < cq) {kq : ℕ}
    (hfloor : ∀ m : ℕ,
      cq / (((m : ℝ) + 1) ^ kq)
        ≤ ‖((R m).basis (j0 m)).gPurity (ρ m)
            * ((R m).basis (j0 m)).gPurity (O m)‖) :
    ¬ HasBarrenPlateau (fun m => (R m).variance)
      ∧ (∀ m, (((F m).matchgateSOHermBasis.dim : ℝ) ≤ 100 * (((m : ℝ) + 1) ^ 2)))
      ∧ ∀ m (Gs : List (Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ)),
          (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (F m).matchgateSOGens).toSubmodule) →
          ((Gs.map NormedSpace.exp).prod * ρ m
              * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O m).trace
            = ∑ j, hsInner ((F m).matchgateSOHermBasis.B j) (gsimEvolved Gs (O m))
                * (ρ m * (F m).matchgateSOHermBasis.B j).trace := by
  have hwhole_dim :
      ∀ m, (((F m).matchgateSOHermBasis.dim : ℝ) ≤ 100 * (((m : ℝ) + 1) ^ 2)) := by
    intro m
    rw [(F m).matchgateSOHermBasis_dim_closedForm]
    norm_num
    nlinarith [sq_nonneg (m : ℝ)]
  have hpoly :
      ¬ HasBarrenPlateau (fun m => (R m).variance)
        ∧ ∀ m (Gs : List (Matrix (Fin (2 ^ (m + 3))) (Fin (2 ^ (m + 3))) ℂ)),
            (∀ A ∈ Gs, A ∈ (dynamicalLieAlgebra (F m).matchgateSOGens).toSubmodule) →
            ((Gs.map NormedSpace.exp).prod * ρ m
                * ((Gs.reverse).map (fun A => NormedSpace.exp (-A))).prod * O m).trace
              = ∑ j, hsInner ((F m).matchgateSOHermBasis.B j) (gsimEvolved Gs (O m))
                  * (ρ m * (F m).matchgateSOHermBasis.B j).trace := by
    refine polyDLA_family_dichotomy
      (sz := fun m => 2 ^ (m + 3))
      (gens := fun m => (F m).matchgateSOGens)
      (ρ := ρ) (O := O)
      (b := fun m => (F m).matchgateSOHermBasis)
      (R := R)
      (CpData := 100) (kpData := 2)
      (j0 := j0)
      (CpIdeal := CpIdeal) (kpIdeal := kpIdeal)
      (cq := cq) (kq := kq)
      hρ hO hdim hOmem hwhole_dim hCpIdeal hdim_j0 hcq hfloor
  exact ⟨hpoly.1, hwhole_dim, hpoly.2⟩

end QuantumAlg
