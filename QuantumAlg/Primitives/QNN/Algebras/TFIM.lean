/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.MatchgateSO
public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Open-chain TFIM dynamical Lie algebra

This module realizes the open-chain TFIM generators in the Jordan--Wigner
Majorana frame.  Consecutive Majorana edges alternate between the physical
fields `Z_j` and couplings `X_j X_{j+1}` and generate the full quadratic
`so(2n)` span.
-/

@[expose] public section

namespace QuantumAlg.TFIM

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Interleaved site/parity coordinates for the `2n` Majorana indices. -/
def majoranaIndexEquiv (n : ℕ) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

@[simp] theorem majoranaIndexEquiv_val {n : ℕ} (p : Fin n × Fin 2) :
    (majoranaIndexEquiv n p).val = p.2.val + 2 * p.1.val := rfl

/-- Jordan--Wigner Majorana label: a `Z` prefix followed by `X` or `Y`. -/
def jwLabel {n : ℕ} (p : Fin n × Fin 2) (k : Fin n) : Fin 4 :=
  if k < p.1 then 3 else if k = p.1 then if p.2 = 0 then 1 else 2 else 0

@[simp] theorem jwLabel_at {n : ℕ} (p : Fin n × Fin 2) :
    jwLabel p p.1 = if p.2 = 0 then 1 else 2 := by
  simp [jwLabel]

theorem jwLabel_of_lt {n : ℕ} (p : Fin n × Fin 2) {k : Fin n} (h : k < p.1) :
    jwLabel p k = 3 := by
  simp [jwLabel, h]

theorem jwLabel_of_gt {n : ℕ} (p : Fin n × Fin 2) {k : Fin n} (h : p.1 < k) :
    jwLabel p k = 0 := by
  simp [jwLabel, not_lt_of_ge h.le, Ne.symm (ne_of_lt h)]

private theorem jwOmega_of_site_lt {n : ℕ} (p q : Fin n × Fin 2) (h : p.1 < q.1) :
    pauliOmega (jwLabel p) (jwLabel q) = 1 := by
  rw [pauliOmega, Finset.sum_eq_single p.1]
  · rw [jwLabel_at, jwLabel_of_lt q h]
    generalize p.2 = r
    fin_cases r <;> simp [omega4]
  · intro k _ hk
    by_cases hkp : k < p.1
    · rw [jwLabel_of_lt p hkp, jwLabel_of_lt q (hkp.trans h)]
      rfl
    · have hpk : p.1 < k := lt_of_le_of_ne (le_of_not_gt hkp) (Ne.symm hk)
      rw [jwLabel_of_gt p hpk]
      generalize jwLabel q k = r
      fin_cases r <;> rfl
  · simp

private theorem jwOmega_same_site {n : ℕ} (p q : Fin n × Fin 2)
    (hsite : p.1 = q.1) (hpq : p ≠ q) :
    pauliOmega (jwLabel p) (jwLabel q) = 1 := by
  have hpar : p.2 ≠ q.2 := by
    intro h
    exact hpq (Prod.ext hsite h)
  rw [pauliOmega, Finset.sum_eq_single p.1]
  · rw [jwLabel_at]
    have hq : q.1 = p.1 := hsite.symm
    rw [← hq, jwLabel_at]
    generalize hp2 : p.2 = r
    generalize hq2 : q.2 = s
    fin_cases r <;> fin_cases s <;> simp [hp2, hq2, omega4] at hpar ⊢
  · intro k _ hk
    by_cases hkp : k < p.1
    · rw [jwLabel_of_lt p hkp, jwLabel_of_lt q (hsite ▸ hkp)]
      rfl
    · have hpk : p.1 < k := lt_of_le_of_ne (le_of_not_gt hkp) (Ne.symm hk)
      rw [jwLabel_of_gt p hpk, jwLabel_of_gt q (hsite ▸ hpk)]
      rfl
  · simp

/-- Distinct Jordan--Wigner Majorana labels anticommute. -/
theorem jwOmega {n : ℕ} (p q : Fin n × Fin 2) (hpq : p ≠ q) :
    pauliOmega (jwLabel p) (jwLabel q) = 1 := by
  rcases lt_trichotomy p.1 q.1 with h | h | h
  · exact jwOmega_of_site_lt p q h
  · exact jwOmega_same_site p q h hpq
  · rw [pauliOmega_comm]
    exact jwOmega_of_site_lt q p h

/-- The concrete Jordan--Wigner Pauli-Majorana frame. -/
def frame (n : ℕ) : PauliMajoranaFrame n where
  v a := jwLabel ((majoranaIndexEquiv n).symm a)
  anti a b hab := by
    apply jwOmega
    intro h
    exact hab ((majoranaIndexEquiv n).symm.injective h)

@[simp] theorem frame_v_index {n : ℕ} (p : Fin n × Fin 2) :
    (frame n).v (majoranaIndexEquiv n p) = jwLabel p := by
  simp [frame]

/-- The physical single-site `Z_j` label. -/
def zLabel {n : ℕ} (j : Fin n) (k : Fin n) : Fin 4 := if k = j then 3 else 0

/-- The physical nearest-neighbor `X_j X_{j+1}` label. -/
def leftSite {n : ℕ} (j : Fin (n - 1)) : Fin n := ⟨j.val, by omega⟩

/-- Right endpoint of the nearest-neighbor edge indexed by `j`. -/
def rightSite {n : ℕ} (j : Fin (n - 1)) : Fin n := ⟨j.val + 1, by omega⟩

/-- Pauli label for the nearest-neighbor `X_j X_{j+1}` term. -/
def xxLabel {n : ℕ} (j : Fin (n - 1)) (k : Fin n) : Fin 4 :=
  if k = leftSite j ∨ k = rightSite j then 1 else 0

/-- The `j`-th field edge is exactly the Pauli `Z_j` label. -/
theorem edgeLabel_field {n : ℕ} (j : Fin n) :
    (frame n).edgeLabel
      s(majoranaIndexEquiv n (j, 0), majoranaIndexEquiv n (j, 1)) = zLabel j := by
  funext k
  simp only [PauliMajoranaFrame.edgeLabel_mk, frame_v_index, pauliXor, zLabel]
  by_cases hlt : k < j
  · rw [jwLabel_of_lt (j, 0) hlt, jwLabel_of_lt (j, 1) hlt]
    simp [ne_of_lt hlt, xor4]
  · by_cases heq : k = j
    · subst heq
      simp [jwLabel, xor4]
    · have hgt : j < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      rw [jwLabel_of_gt (j, 0) hgt, jwLabel_of_gt (j, 1) hgt]
      simp [heq, xor4]

/-- The edge between neighboring sites is exactly `X_j X_{j+1}`. -/
theorem edgeLabel_coupling {n : ℕ} (j : Fin (n - 1)) :
    (frame n).edgeLabel
      s(majoranaIndexEquiv n (leftSite j, 1), majoranaIndexEquiv n (rightSite j, 0)) =
        xxLabel j := by
  funext k
  simp only [PauliMajoranaFrame.edgeLabel_mk, frame_v_index, pauliXor]
  by_cases hleft : k = leftSite j
  · subst hleft
    simp [jwLabel, xxLabel, leftSite, rightSite, xor4]
  · by_cases hright : k = rightSite j
    · subst hright
      simp [jwLabel, xxLabel, leftSite, rightSite, xor4]
    · have hcases : k < leftSite j ∨ rightSite j < k := by
        rcases lt_trichotomy k (leftSite j) with h | h | h
        · exact Or.inl h
        · exact (hleft h).elim
        · right
          have hrightVal : k.val ≠ j.val + 1 := by
            intro hv
            apply hright
            apply Fin.ext
            simpa [rightSite] using hv
          change j.val + 1 < k.val
          change j.val < k.val at h
          omega
      rcases hcases with hlt | hgt
      · rw [jwLabel_of_lt (leftSite j, 1) hlt,
          jwLabel_of_lt (rightSite j, 0) (hlt.trans (by simp [leftSite, rightSite]))]
        simp [xxLabel, hleft, hright, xor4]
      · rw [jwLabel_of_gt (leftSite j, 1) (by
            exact (by simp [leftSite, rightSite] : leftSite j < rightSite j) |>.trans hgt),
          jwLabel_of_gt (rightSite j, 0) hgt]
        simp [xxLabel, hleft, hright, xor4]

/-- The path graph on the interleaved `2n` Majorana indices. -/
def majoranaPath (n : ℕ) : SimpleGraph (Fin (2 * n)) :=
  SimpleGraph.pathGraph (2 * n)

/-- The Majorana path is connected whenever the physical chain is nonempty. -/
theorem majoranaPath_connected {n : ℕ} (hn : 1 ≤ n) : (majoranaPath n).Connected := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold majoranaPath
  rw [show 2 * (1 + m) = (2 * m + 1) + 1 by omega]
  exact SimpleGraph.pathGraph_connected (2 * m + 1)

/-- Open-chain TFIM generators, expressed as consecutive Jordan--Wigner Majorana edges. -/
def gens (n : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  (frame n).graphGens (majoranaPath n)

/-- The physical transverse-field generator `i Z_j`. -/
noncomputable def fieldGen {n : ℕ} (j : Fin n) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Complex.I • pauliMat (zLabel j)

/-- The physical Ising-coupling generator `i X_j X_{j+1}`. -/
noncomputable def couplingGen {n : ℕ} (j : Fin (n - 1)) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  Complex.I • pauliMat (xxLabel j)

/-- The physical `{iZ_j, iX_jX_{j+1}}` generator family. -/
def physicalGens (n : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  Set.range fieldGen ∪ Set.range couplingGen

theorem fieldGen_mem_gens {n : ℕ} (j : Fin n) : fieldGen j ∈ gens n := by
  refine ⟨⟨s(majoranaIndexEquiv n (j, 0), majoranaIndexEquiv n (j, 1)), ?_⟩, ?_⟩
  · rw [SimpleGraph.mem_edgeSet, majoranaPath, SimpleGraph.pathGraph_adj]
    left
    simp
    omega
  · change Complex.I • pauliMat (zLabel j) = Complex.I • pauliMat
      ((frame n).edgeLabel s(majoranaIndexEquiv n (j, 0), majoranaIndexEquiv n (j, 1)))
    rw [edgeLabel_field]

theorem couplingGen_mem_gens {n : ℕ} (j : Fin (n - 1)) : couplingGen j ∈ gens n := by
  refine ⟨⟨s(majoranaIndexEquiv n (leftSite j, 1),
      majoranaIndexEquiv n (rightSite j, 0)), ?_⟩, ?_⟩
  · rw [SimpleGraph.mem_edgeSet, majoranaPath, SimpleGraph.pathGraph_adj]
    left
    simp [leftSite, rightSite]
    omega
  · change Complex.I • pauliMat (xxLabel j) = Complex.I • pauliMat
      ((frame n).edgeLabel s(majoranaIndexEquiv n (leftSite j, 1),
        majoranaIndexEquiv n (rightSite j, 0)))
    rw [edgeLabel_coupling]

theorem physicalGens_subset_gens (n : ℕ) : physicalGens n ⊆ gens n := by
  rintro A (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · exact fieldGen_mem_gens j
  · exact couplingGen_mem_gens j

theorem gens_subset_physicalGens (n : ℕ) : gens n ⊆ physicalGens n := by
  have hconsecutive : ∀ a b : Fin (2 * n), a.val + 1 = b.val →
      Complex.I • pauliMat ((frame n).edgeLabel s(a, b)) ∈ physicalGens n := by
    intro a b hab
    have hmod : a.val % 2 = 0 ∨ a.val % 2 = 1 := by omega
    rcases hmod with heven | hodd
    · have hadecomp : a.val = 2 * (a.val / 2) := by omega
      let j : Fin n := ⟨a.val / 2, by omega⟩
      have ha : a = majoranaIndexEquiv n (j, 0) := by
        apply Fin.ext
        simp only [majoranaIndexEquiv_val, Fin.val_zero, zero_add]
        dsimp [j]
        omega
      have hb : b = majoranaIndexEquiv n (j, 1) := by
        apply Fin.ext
        simp only [majoranaIndexEquiv_val, Fin.val_one]
        dsimp [j]
        omega
      rw [ha, hb]
      left
      refine ⟨j, ?_⟩
      rw [edgeLabel_field]
      rfl
    · have hadecomp : a.val = 2 * (a.val / 2) + 1 := by omega
      let j : Fin (n - 1) := ⟨a.val / 2, by omega⟩
      have ha : a = majoranaIndexEquiv n (leftSite j, 1) := by
        apply Fin.ext
        simp only [majoranaIndexEquiv_val, Fin.val_one]
        dsimp [leftSite, j]
        omega
      have hb : b = majoranaIndexEquiv n (rightSite j, 0) := by
        apply Fin.ext
        simp only [majoranaIndexEquiv_val, Fin.val_zero, zero_add]
        dsimp [rightSite, j]
        omega
      rw [ha, hb]
      right
      refine ⟨j, ?_⟩
      rw [edgeLabel_coupling]
      rfl
  rintro A ⟨⟨z, hz⟩, rfl⟩
  induction z using Sym2.inductionOn with
  | hf a b =>
      have hab := (SimpleGraph.mem_edgeSet (majoranaPath n)).mp hz
      rw [majoranaPath, SimpleGraph.pathGraph_adj] at hab
      rcases hab with hab | hba
      · exact hconsecutive a b hab
      · have h := hconsecutive b a hba
        simpa only [PauliMajoranaFrame.edgeLabel_mk, pauliXor_comm] using h

/-- The path-edge and physical `{iZ_j,iX_jX_{j+1}}` descriptions coincide. -/
theorem physicalGens_eq_gens (n : ℕ) : physicalGens n = gens n :=
  Set.Subset.antisymm (physicalGens_subset_gens n) (gens_subset_physicalGens n)

/-- Consequently the physical TFIM generators have the full quadratic `so(2n)` Lie closure. -/
theorem physical_dla_toSubmodule {n : ℕ} (hn : 1 ≤ n) :
    (dynamicalLieAlgebra (physicalGens n)).toSubmodule =
      Submodule.span ℂ (frame n).matchgateSOPauliSet := by
  rw [physicalGens_eq_gens]
  exact (frame n).graph_dla_toSubmodule (majoranaPath n) (majoranaPath_connected hn)

/-- The Hermitian orthonormal `so(2n)` basis generated by the open-chain TFIM. -/
noncomputable def hermBasis (n : ℕ) (hn : 1 ≤ n) : DLAHermBasis (gens n) :=
  (frame n).graphHermBasis (majoranaPath n) (majoranaPath_connected hn)

@[simp] theorem hermBasis_B (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (Fintype.card (MatchgateSOEdge n))) :
    (hermBasis n hn).B i = (frame n).matchgateSOB i := rfl

/-- The open-chain TFIM DLA has dimension `n(2n-1)`. -/
theorem hermBasis_dim (n : ℕ) (hn : 1 ≤ n) :
    (hermBasis n hn).dim = n * (2 * n - 1) := by
  change Fintype.card (MatchgateSOEdge n) = n * (2 * n - 1)
  exact matchgateSOEdge_card n

/-- Schur identity for the simple open-chain TFIM DLA (`n≥3`). -/
theorem hermBasis_schur {n : ℕ} (hn : 3 ≤ n) :
    gTensorGInvariant (hermBasis n (by omega)) =
      Submodule.span ℂ {(hermBasis n (by omega)).casimir} := by
  change gTensorGInvariant (frame n).matchgateSOHermBasis =
    Submodule.span ℂ {(frame n).matchgateSOHermBasis.casimir}
  exact matchgateSOHermBasis_schur (frame n) hn

end QuantumAlg.TFIM
