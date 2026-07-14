/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.QNN.Algebras.TFIM
public import QuantumAlg.Primitives.QNN.Algebras.SingleQubitDLA
public import QuantumAlg.Primitives.QNN.Simulation.ClassicalDLAScaling

/-!
# Highest-weight scaling for the open-chain TFIM

The all-zero computational state is the spin-representation highest-weight
state.  For the quadratic `so(2n)` DLA its exact `g`-purity is `n/2^n`.
The Setup-1 observable is kept unnormalized, giving `g`-purity `2^n` and hence
the exact second moment `1/(2n-1)` for any supplied `RagoneSecondMoment`.

The explicit consistency witness below is algebraic only: it is not presented
as a TFIM Haar twirl or finite two-design.
-/

@[expose] public section

namespace QuantumAlg.TFIMWeightScaling

open Matrix

/-- The all-zero highest-weight state. -/
noncomputable abbrev state (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  localState

private theorem jwEdgeAmplitude_same_site {n : ℕ} (p q : Fin n × Fin 2)
    (hsite : p.1 = q.1) (hpq : p ≠ q) :
    (∏ k, pauli1 (pauliXor (TFIM.jwLabel p) (TFIM.jwLabel q) k) 0 0) = 1 := by
  have hpar : p.2 ≠ q.2 := by
    intro h
    exact hpq (Prod.ext hsite h)
  apply Finset.prod_eq_one
  intro k _
  simp only [pauliXor]
  by_cases hlt : k < p.1
  · rw [TFIM.jwLabel_of_lt p hlt, TFIM.jwLabel_of_lt q (hsite ▸ hlt)]
    rfl
  · by_cases heq : k = p.1
    · subst heq
      have hqat : TFIM.jwLabel q p.1 = if q.2 = 0 then 1 else 2 := by
        rw [hsite]
        exact TFIM.jwLabel_at q
      rw [TFIM.jwLabel_at, hqat]
      generalize hp2 : p.2 = r
      generalize hq2 : q.2 = s
      fin_cases r <;> fin_cases s <;>
        simp [hp2, hq2, xor4, pauli1, pauliZ] at hpar ⊢
    · have hgt : p.1 < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      rw [TFIM.jwLabel_of_gt p hgt, TFIM.jwLabel_of_gt q (hsite ▸ hgt)]
      rfl

private theorem jwEdgeAmplitude_of_site_lt {n : ℕ} (p q : Fin n × Fin 2)
    (hsite : p.1 < q.1) :
    (∏ k, pauli1 (pauliXor (TFIM.jwLabel p) (TFIM.jwLabel q) k) 0 0) = 0 := by
  rw [Finset.prod_eq_zero (Finset.mem_univ p.1)]
  simp only [pauliXor]
  rw [TFIM.jwLabel_at, TFIM.jwLabel_of_lt q hsite]
  generalize hp2 : p.2 = r
  fin_cases r <;> simp [xor4, pauli1, pauliX, pauliY]

private theorem jwEdgeAmplitude {n : ℕ} (p q : Fin n × Fin 2) (hpq : p ≠ q) :
    (∏ k, pauli1 (pauliXor (TFIM.jwLabel p) (TFIM.jwLabel q) k) 0 0) =
      if p.1 = q.1 then 1 else 0 := by
  by_cases hsite : p.1 = q.1
  · rw [if_pos hsite]
    exact jwEdgeAmplitude_same_site p q hsite hpq
  · rw [if_neg hsite]
    rcases lt_or_gt_of_ne hsite with h | h
    · exact jwEdgeAmplitude_of_site_lt p q h
    · rw [pauliXor_comm]
      exact jwEdgeAmplitude_of_site_lt q p h

/-- The site underlying a Majorana index. -/
def majoranaSite {n : ℕ} (a : Fin (2 * n)) : Fin n :=
  ((TFIM.majoranaIndexEquiv n).symm a).1

private theorem edgeAmplitude {n : ℕ} (a b : Fin (2 * n)) (hab : a ≠ b) :
    (∏ k, pauli1 ((TFIM.frame n).edgeLabel s(a, b) k) 0 0) =
      if majoranaSite a = majoranaSite b then 1 else 0 := by
  let p := (TFIM.majoranaIndexEquiv n).symm a
  let q := (TFIM.majoranaIndexEquiv n).symm b
  have hpq : p ≠ q := by
    intro h
    exact hab ((TFIM.majoranaIndexEquiv n).symm.injective h)
  change (∏ k, pauli1 (pauliXor (TFIM.jwLabel p) (TFIM.jwLabel q) k) 0 0) =
    if p.1 = q.1 then 1 else 0
  exact jwEdgeAmplitude p q hpq

/-- Whether a quadratic Majorana edge pairs the two modes at one physical site. -/
def sameSiteEdge {n : ℕ} (e : MatchgateSOEdge n) : Prop :=
  Sym2.lift ⟨fun a b => majoranaSite a = majoranaSite b, by
    intro a b
    apply propext
    exact eq_comm⟩ e.1

noncomputable instance sameSiteEdgeDecidable {n : ℕ} (e : MatchgateSOEdge n) :
    Decidable (sameSiteEdge e) := Classical.propDecidable _

/-- The complete-graph edge pairing the `X` and `Y` Majoranas at site `j`. -/
def fieldEdge {n : ℕ} (j : Fin n) : MatchgateSOEdge n :=
  matchgateSOEdgeOfNe
    (TFIM.majoranaIndexEquiv n (j, 0)) (TFIM.majoranaIndexEquiv n (j, 1)) (by
      intro h
      have hv := congrArg Fin.val h
      simp at hv)

@[simp] theorem sameSiteEdge_fieldEdge {n : ℕ} (j : Fin n) :
    sameSiteEdge (fieldEdge j) := by
  simp [sameSiteEdge, fieldEdge, majoranaSite]

theorem zLabel_injective {n : ℕ} : Function.Injective (@TFIM.zLabel n) := by
  intro j k h
  by_contra hjk
  have hv := congrFun h j
  simp [TFIM.zLabel, hjk] at hv

theorem fieldEdge_injective {n : ℕ} : Function.Injective (@fieldEdge n) := by
  intro j k h
  apply zLabel_injective
  rw [← TFIM.edgeLabel_field j, ← TFIM.edgeLabel_field k]
  exact congrArg (TFIM.frame n).edgeLabel (Subtype.ext_iff.mp h)

theorem fieldEdge_surjective {n : ℕ} :
    Function.Surjective (fun j : Fin n =>
      (⟨fieldEdge j, sameSiteEdge_fieldEdge j⟩ : {e : MatchgateSOEdge n // sameSiteEdge e})) := by
  rintro ⟨⟨z, hz⟩, hsite⟩
  induction z using Sym2.inductionOn with
  | hf a b =>
      let p := (TFIM.majoranaIndexEquiv n).symm a
      let q := (TFIM.majoranaIndexEquiv n).symm b
      have hab : a ≠ b := by
        intro h
        subst h
        exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz)
          (by rw [Sym2.mk_isDiag_iff])
      have hpq : p ≠ q := by
        intro h
        exact hab ((TFIM.majoranaIndexEquiv n).symm.injective h)
      have hpqSite : p.1 = q.1 := hsite
      have hpar : p.2 ≠ q.2 := by
        intro h
        exact hpq (Prod.ext hpqSite h)
      generalize hp2 : p.2 = r
      generalize hq2 : q.2 = s
      fin_cases r <;> fin_cases s
      · simp [hp2, hq2] at hpar
      · refine ⟨p.1, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change (fieldEdge p.1).1 = s(a, b)
        have ha : a = TFIM.majoranaIndexEquiv n (p.1, 0) := by
          calc
            a = TFIM.majoranaIndexEquiv n p :=
              (TFIM.majoranaIndexEquiv n).apply_symm_apply a |>.symm
            _ = TFIM.majoranaIndexEquiv n (p.1, 0) := by
              congr 2
              exact Prod.ext rfl hp2
        have hb : b = TFIM.majoranaIndexEquiv n (p.1, 1) := by
          calc
            b = TFIM.majoranaIndexEquiv n q :=
              (TFIM.majoranaIndexEquiv n).apply_symm_apply b |>.symm
            _ = TFIM.majoranaIndexEquiv n (p.1, 1) := by
              congr 2
              exact Prod.ext hpqSite.symm hq2
        rw [ha, hb]
        rfl
      · refine ⟨p.1, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        change (fieldEdge p.1).1 = s(a, b)
        have ha : a = TFIM.majoranaIndexEquiv n (p.1, 1) := by
          calc
            a = TFIM.majoranaIndexEquiv n p :=
              (TFIM.majoranaIndexEquiv n).apply_symm_apply a |>.symm
            _ = TFIM.majoranaIndexEquiv n (p.1, 1) := by
              congr 2
              exact Prod.ext rfl hp2
        have hb : b = TFIM.majoranaIndexEquiv n (p.1, 0) := by
          calc
            b = TFIM.majoranaIndexEquiv n q :=
              (TFIM.majoranaIndexEquiv n).apply_symm_apply b |>.symm
            _ = TFIM.majoranaIndexEquiv n (p.1, 0) := by
              congr 2
              exact Prod.ext hpqSite.symm hq2
        rw [ha, hb]
        exact Sym2.eq_swap
      · simp [hp2, hq2] at hpar

/-- Same-site quadratic edges are in bijection with physical sites. -/
noncomputable def sameSiteEdgeEquiv {n : ℕ} :
    Fin n ≃ {e : MatchgateSOEdge n // sameSiteEdge e} :=
  Equiv.ofBijective
    (fun j => ⟨fieldEdge j, sameSiteEdge_fieldEdge j⟩)
    ⟨fun _ _ h => fieldEdge_injective (Subtype.ext_iff.mp h), fieldEdge_surjective⟩

theorem sameSiteEdge_card (n : ℕ) :
    Fintype.card {e : MatchgateSOEdge n // sameSiteEdge e} = n := by
  classical
  rw [Fintype.card_congr (sameSiteEdgeEquiv (n := n)).symm, Fintype.card_fin]

private theorem sum_sameSiteEdge_indicator (n : ℕ) (c : ℂ) :
    (∑ e : MatchgateSOEdge n, if sameSiteEdge e then c else 0) = (n : ℂ) * c := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun e : MatchgateSOEdge n => sameSiteEdge e).card = n := by
    rw [← Fintype.card_subtype]
    exact sameSiteEdge_card n
  rw [hcard]

private theorem hsInner_basis_state (n : ℕ) (hn : 1 ≤ n)
    (i : Fin (Fintype.card (MatchgateSOEdge n))) :
    hsInner ((TFIM.hermBasis n hn).B i) (state n) =
      rtNinv n * (if sameSiteEdge
        (PauliMajoranaFrame.matchgateSOEdgeEquiv (n := n) i) then 1 else 0) := by
  classical
  rw [TFIM.hermBasis_B]
  change hsInner
      (rtNinv n • pauliMat ((TFIM.frame n).edgeLabel
        ((PauliMajoranaFrame.matchgateSOEdgeEquiv (n := n) i).1))) localState = _
  rw [hsInner_smul_left, hsInner_pauliMat_localState, starRingEnd_apply, rtNinv_conj]
  let e := PauliMajoranaFrame.matchgateSOEdgeEquiv (n := n) i
  change rtNinv n * (starRingEnd ℂ)
      (∏ l, pauli1 ((TFIM.frame n).edgeLabel e.1 l) 0 0) =
    rtNinv n * (if sameSiteEdge e then 1 else 0)
  cases e with
  | mk z hz =>
      induction z using Sym2.inductionOn with
      | hf a b =>
          have hab : a ≠ b := by
            intro h
            subst h
            exact (SimpleGraph.not_isDiag_of_mem_edgeSet (⊤ : SimpleGraph (Fin (2 * n))) hz)
              (by rw [Sym2.mk_isDiag_iff])
          rw [edgeAmplitude a b hab]
          by_cases hsite : majoranaSite a = majoranaSite b <;>
            simp [hsite, sameSiteEdge]

/-- Exact highest-weight-state purity `P_g(ρ)=n/2^n`. -/
theorem state_gPurity (n : ℕ) (hn : 1 ≤ n) :
    (TFIM.hermBasis n hn).gPurity (state n) = (n : ℂ) / (2 ^ n : ℂ) := by
  classical
  change (∑ i : Fin (Fintype.card (MatchgateSOEdge n)),
      (Complex.normSq (hsInner ((TFIM.hermBasis n hn).B i) (state n)) : ℂ)) = _
  simp_rw [hsInner_basis_state n hn]
  have hterm : ∀ e : MatchgateSOEdge n,
      (Complex.normSq (rtNinv n * (if sameSiteEdge e then 1 else 0)) : ℂ) =
        if sameSiteEdge e then (2 ^ n : ℂ)⁻¹ else 0 := by
    intro e
    split_ifs <;> simp [hrtNormSq]
  have hreindex := Equiv.sum_comp (PauliMajoranaFrame.matchgateSOEdgeEquiv (n := n))
    (fun e : MatchgateSOEdge n =>
      (Complex.normSq (rtNinv n * (if sameSiteEdge e then 1 else 0)) : ℂ))
  rw [hreindex]
  simp_rw [hterm]
  rw [sum_sameSiteEdge_indicator]
  field_simp

/-- Index of the normalized Cartan element `Z_j`. -/
noncomputable def cartanIndex {n : ℕ} (j : Fin n) :
    Fin (Fintype.card (MatchgateSOEdge n)) :=
  PauliMajoranaFrame.matchgateSOEdgeEquiv.symm (fieldEdge j)

/-- Normalized Cartan basis element associated with site `j`. -/
noncomputable def cartanB (n : ℕ) (hn : 1 ≤ n) (j : Fin n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  (TFIM.hermBasis n hn).B (cartanIndex j)

private theorem cartanIndex_injective {n : ℕ} : Function.Injective (@cartanIndex n) := by
  intro j k h
  apply fieldEdge_injective
  exact PauliMajoranaFrame.matchgateSOEdgeEquiv.symm.injective h

private theorem gProj_state_eq (n : ℕ) (hn : 1 ≤ n) :
    (TFIM.hermBasis n hn).gProj (state n) =
      ∑ j : Fin n, rtNinv n • cartanB n hn j := by
  classical
  change (∑ i : Fin (Fintype.card (MatchgateSOEdge n)),
      hsInner ((TFIM.hermBasis n hn).B i) (state n) • (TFIM.hermBasis n hn).B i) = _
  simp_rw [hsInner_basis_state n hn, TFIM.hermBasis_B]
  let f : MatchgateSOEdge n → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ := fun e =>
    (rtNinv n * (if sameSiteEdge e then 1 else 0)) •
      (TFIM.frame n).matchgateSOB (PauliMajoranaFrame.matchgateSOEdgeEquiv.symm e)
  calc
    (∑ i : Fin (Fintype.card (MatchgateSOEdge n)),
        (rtNinv n * (if sameSiteEdge (PauliMajoranaFrame.matchgateSOEdgeEquiv i) then 1 else 0)) •
          (TFIM.frame n).matchgateSOB i) = ∑ e : MatchgateSOEdge n, f e := by
      rw [← Equiv.sum_comp (PauliMajoranaFrame.matchgateSOEdgeEquiv (n := n))]
      apply Finset.sum_congr rfl
      intro i _
      simp [f]
    _ = (∑ e ∈ Finset.univ.filter sameSiteEdge,
        rtNinv n • (TFIM.frame n).matchgateSOB
          (PauliMajoranaFrame.matchgateSOEdgeEquiv.symm e)) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : sameSiteEdge e <;> simp [f, he]
    _ = (∑ e : {e : MatchgateSOEdge n // sameSiteEdge e},
        rtNinv n • (TFIM.frame n).matchgateSOB
          (PauliMajoranaFrame.matchgateSOEdgeEquiv.symm e.1)) := by
      apply Finset.sum_subtype
      intro e
      simp
    _ = (∑ j : Fin n, rtNinv n • cartanB n hn j) := by
      rw [← Equiv.sum_comp (sameSiteEdgeEquiv (n := n))
        (fun e : {e : MatchgateSOEdge n // sameSiteEdge e} =>
          rtNinv n • (TFIM.frame n).matchgateSOB
            (PauliMajoranaFrame.matchgateSOEdgeEquiv.symm e.1))]
      apply Finset.sum_congr rfl
      intro j _
      simp [sameSiteEdgeEquiv, cartanB, cartanIndex]

/-- Cartan-coordinate `WeightStateData` for the highest-weight state. -/
noncomputable def weightData (n : ℕ) (hn : 1 ≤ n) :
    WeightStateData (TFIM.hermBasis n hn) (state n) where
  dimH := n
  H := cartanB n hn
  H_herm := fun j => (TFIM.hermBasis n hn).herm (cartanIndex j)
  H_ortho := fun i j => by
    unfold cartanB
    rw [(TFIM.hermBasis n hn).ortho]
    by_cases h : i = j
    · subst j
      simp
    · have hidx : cartanIndex i ≠ cartanIndex j := fun hij => h (cartanIndex_injective hij)
      rw [if_neg h]
      exact if_neg hidx
  lam := fun _ => (Real.sqrt (2 ^ n))⁻¹
  proj_eq := by
    rw [gProj_state_eq]
    apply Finset.sum_congr rfl
    intro j _
    rfl

/-- The endpoint Majorana edge used by Ragone Setup 1. -/
def observableEdge (n : ℕ) (hn : 2 ≤ n) : MatchgateSOEdge n :=
  let a := TFIM.majoranaIndexEquiv n (⟨0, by omega⟩, 1)
  let b := TFIM.majoranaIndexEquiv n (⟨n - 1, by omega⟩, 1)
  matchgateSOEdgeOfNe a b (by
    apply Fin.ne_of_val_ne
    simp [a, b]
    omega)

/-- Pauli label `X₁ Z₂ ⋯ Zₙ₋₁ Yₙ` for Ragone Setup 1. -/
def setup1Label (n : ℕ) (hn : 2 ≤ n) (k : Fin n) : Fin 4 :=
  if k = ⟨0, by omega⟩ then 1 else if k = ⟨n - 1, by omega⟩ then 2 else 3

/-- The endpoint Majorana edge is exactly the Setup-1 label `X₁ Z₂ ⋯ Zₙ₋₁ Yₙ`. -/
theorem observableEdge_label (n : ℕ) (hn : 2 ≤ n) :
    (TFIM.frame n).edgeLabel (observableEdge n hn).1 = setup1Label n hn := by
  simp only [observableEdge, matchgateSOEdgeOfNe_val,
    PauliMajoranaFrame.edgeLabel_mk, TFIM.frame_v_index]
  funext k
  by_cases hk0 : k = ⟨0, by omega⟩
  · have hzeroLast : (⟨0, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
      change 0 < n - 1
      omega
    rw [hk0, pauliXor, TFIM.jwLabel_at,
      TFIM.jwLabel_of_lt (⟨n - 1, by omega⟩, 1) hzeroLast]
    simp [setup1Label, xor4]
  · by_cases hklast : k = ⟨n - 1, by omega⟩
    · have hzeroLast : (⟨0, by omega⟩ : Fin n) < ⟨n - 1, by omega⟩ := by
        change 0 < n - 1
        omega
      have hlast0 : n - 1 ≠ 0 := by omega
      rw [hklast, pauliXor,
        TFIM.jwLabel_of_gt (⟨0, by omega⟩, 1) hzeroLast, TFIM.jwLabel_at]
      simp [setup1Label, xor4, Fin.ext_iff, hlast0]
    · have hk0val : k.val ≠ 0 := by
        intro h
        apply hk0
        apply Fin.ext
        simpa using h
      have hklastval : k.val ≠ n - 1 := by
        intro h
        apply hklast
        apply Fin.ext
        simpa using h
      have hmid : 0 < k.val ∧ k.val < n - 1 := by omega
      have hzeroK : (⟨0, by omega⟩ : Fin n) < k := by
        change 0 < k.val
        exact hmid.1
      have hkLast : k < (⟨n - 1, by omega⟩ : Fin n) := by
        change k.val < n - 1
        exact hmid.2
      rw [pauliXor, TFIM.jwLabel_of_gt (⟨0, by omega⟩, 1) hzeroK,
        TFIM.jwLabel_of_lt (⟨n - 1, by omega⟩, 1) hkLast]
      simp [setup1Label, hk0, hklast, xor4]

/-- The unnormalized Setup-1 `\widehat{X_1Y_n}` Majorana quadratic. -/
noncomputable def observable (n : ℕ) (hn : 2 ≤ n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  pauliMat ((TFIM.frame n).edgeLabel (observableEdge n hn).1)

/-- The observable matrix is exactly the Pauli string `X₁ Z₂ ⋯ Zₙ₋₁ Yₙ`. -/
theorem observable_eq_setup1Label (n : ℕ) (hn : 2 ≤ n) :
    observable n hn = pauliMat (setup1Label n hn) := by
  rw [observable, observableEdge_label]

theorem observable_herm (n : ℕ) (hn : 2 ≤ n) :
    (observable n hn)ᴴ = observable n hn := pauliMat_isHermitian _

/-- Basis index of the Setup-1 endpoint quadratic. -/
noncomputable def observableIndex (n : ℕ) (hn : 2 ≤ n) :
    Fin (Fintype.card (MatchgateSOEdge n)) :=
  PauliMajoranaFrame.matchgateSOEdgeEquiv.symm (observableEdge n hn)

theorem observable_eq_smul_basis (n : ℕ) (hn : 2 ≤ n) :
    observable n hn = (rtNinv n)⁻¹ • (TFIM.hermBasis n (by omega)).B
      (observableIndex n hn) := by
  rw [TFIM.hermBasis_B]
  have hidx : PauliMajoranaFrame.matchgateSOEdgeEquiv (observableIndex n hn) =
      observableEdge n hn := by
    exact Equiv.apply_symm_apply _ _
  change pauliMat ((TFIM.frame n).edgeLabel (observableEdge n hn).1) =
    (rtNinv n)⁻¹ • (rtNinv n • pauliMat ((TFIM.frame n).edgeLabel
      ((PauliMajoranaFrame.matchgateSOEdgeEquiv (observableIndex n hn)).1)))
  rw [hidx, smul_smul, inv_mul_cancel₀ (rtNinv_ne_zero n), one_smul]

/-- The unnormalized Setup-1 observable has exact purity `P_g(O)=2^n`. -/
theorem observable_gPurity (n : ℕ) (hn : 2 ≤ n) :
    (TFIM.hermBasis n (by omega)).gPurity (observable n hn) = (2 ^ n : ℂ) := by
  rw [observable_eq_smul_basis, gPurity_smul,
    DLAHermBasis.gPurity_basis_elem, mul_one, hrtNormSqInv]

/-- For any supplied Ragone second moment, the exact value is `1/(2n-1)`. -/
theorem secondMoment_eq {n : ℕ} (hn : 3 ≤ n)
    (M : RagoneSecondMoment (TFIM.hermBasis n (by omega)) (state n)
      (observable n (by omega))) :
    M.variance = 1 / (2 * n - 1 : ℝ) := by
  apply Complex.ofReal_injective
  rw [M.variance_eq_gPurity localState_herm (observable_herm n (by omega)) (by
      rw [TFIM.hermBasis_dim]
      exact Nat.mul_pos (by omega) (by omega)), state_gPurity, observable_gPurity,
    TFIM.hermBasis_dim]
  push_cast
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hdenC : ((2 * n - 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
  push_cast
  field_simp [hnC, hdenC]

/-- Algebraic consistency witness only; this is not a TFIM Haar/2-design construction. -/
noncomputable def nonphysicalConsistencyWitness (n : ℕ) (hn : 3 ≤ n) :
    RagoneSecondMoment (TFIM.hermBasis n (by omega)) (state n)
      (observable n (by omega)) :=
  RagoneSecondMoment.consistencyWitness localState_herm
    (observable_herm n (by omega)) (by
      rw [TFIM.hermBasis_dim]
      exact Nat.mul_pos (by omega) (by omega)) (TFIM.hermBasis_schur hn)

/-- **Open-chain TFIM highest-weight endpoint:** inverse-linear variance rules out a barren plateau.
-/
theorem main
    (M : (m : ℕ) → RagoneSecondMoment (TFIM.hermBasis (m + 3) (by omega))
      (state (m + 3)) (observable (m + 3) (by omega))) :
    ¬ HasBarrenPlateau (fun m => (M m).variance) := by
  apply not_hasBarrenPlateau_of_invPoly_lower _ (c := (1 : ℝ) / 5) (k := 1)
  · norm_num
  · intro m
    rw [secondMoment_eq (n := m + 3) (by omega) (M m)]
    norm_num [pow_one, div_div]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hden : 0 < (2 * ((m : ℝ) + 3) - 1) := by
      nlinarith
    have hle : 2 * ((m : ℝ) + 3) - 1 ≤ 5 * ((m : ℝ) + 1) := by
      nlinarith
    calc
      ((m : ℝ) + 1)⁻¹ * (1 / 5) = 1 / (5 * ((m : ℝ) + 1)) := by
        field_simp
      _ ≤ 1 / (2 * ((m : ℝ) + 3) - 1) := by
        exact one_div_le_one_div_of_le hden hle
      _ = (2 * ((m : ℝ) + 3) - 1)⁻¹ := one_div _

end QuantumAlg.TFIMWeightScaling
