/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Polynomial.Complement.Interval.Certificate
public import QuantumAlg.Init
public import QuantumAlg.Util.Complex
public import QuantumAlg.Util.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Interval square decompositions

Quantum-free polynomial certificates used by the source-aligned QSVT proof
path.  The source-facing target is the even interval-nonnegative decomposition
in Gilyen--Su--Low--Wiebe [GSLW19, BlockHam.tex:436-480].
-/

@[expose] public section

namespace QuantumAlg

open Polynomial

namespace Complement.Interval

private theorem multiset_count_le_countP_of {α : Type*} [DecidableEq α]
    (s : Multiset α) {a : α} {p : α → Prop} [DecidablePred p] (ha : p a) :
    s.count a ≤ s.countP p := by
  rw [Multiset.count_eq_card_filter_eq, Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card
    (Multiset.monotone_filter_right s (fun x hx => by
      rw [← hx]
      exact ha))

private theorem multiset_countP_or_eq_add {α : Type*} {p q : α → Prop}
    (s : Multiset α)
    (hdisj : ∀ x, p x → q x → False) :
    @Multiset.countP α (fun x => p x ∨ q x)
      (fun x => Classical.propDecidable (p x ∨ q x)) s =
      @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
        @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s := by
  classical
  refine Multiset.induction_on s ?h0 ?hcons
  · simp
  · intro a s ih
    by_cases hp : p a
    · have hnq : ¬ q a := fun hq => hdisj a hp hq
      simp [hp, hnq, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · by_cases hq : q a
      · simp [hp, hq, ih, Nat.add_assoc]
      · simp [hp, hq, ih]

private theorem multiset_countP_or4_eq_add {α : Type*}
    {p q r t : α → Prop}
    (s : Multiset α)
    (hpq : ∀ x, p x → q x → False)
    (hpr : ∀ x, p x → r x → False)
    (hpt : ∀ x, p x → t x → False)
    (hqr : ∀ x, q x → r x → False)
    (hqt : ∀ x, q x → t x → False)
    (hrt : ∀ x, r x → t x → False) :
    @Multiset.countP α (fun x => p x ∨ q x ∨ r x ∨ t x)
      (fun x => Classical.propDecidable (p x ∨ q x ∨ r x ∨ t x)) s =
      @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
        @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
          @Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
            @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s := by
  classical
  calc
    @Multiset.countP α (fun x => p x ∨ q x ∨ r x ∨ t x)
      (fun x => Classical.propDecidable (p x ∨ q x ∨ r x ∨ t x)) s =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          @Multiset.countP α (fun x => q x ∨ r x ∨ t x)
            (fun x => Classical.propDecidable (q x ∨ r x ∨ t x)) s := by
      exact multiset_countP_or_eq_add s
        (fun x hp hrest => by
          rcases hrest with hq | hr | ht
          · exact hpq x hp hq
          · exact hpr x hp hr
          · exact hpt x hp ht)
    _ =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          (@Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
            @Multiset.countP α (fun x => r x ∨ t x)
              (fun x => Classical.propDecidable (r x ∨ t x)) s) := by
      rw [multiset_countP_or_eq_add s
        (fun x hq hrest => by
          rcases hrest with hr | ht
          · exact hqr x hq hr
          · exact hqt x hq ht)]
    _ =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          (@Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
            (@Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
              @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s)) := by
      rw [multiset_countP_or_eq_add s hrt]
    _ =
      @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
            @Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
              @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s := by
      omega

private theorem multiset_countP_or5_eq_add {α : Type*}
    {p q r t u : α → Prop}
    (s : Multiset α)
    (hpq : ∀ x, p x → q x → False)
    (hpr : ∀ x, p x → r x → False)
    (hpt : ∀ x, p x → t x → False)
    (hpu : ∀ x, p x → u x → False)
    (hqr : ∀ x, q x → r x → False)
    (hqt : ∀ x, q x → t x → False)
    (hqu : ∀ x, q x → u x → False)
    (hrt : ∀ x, r x → t x → False)
    (hru : ∀ x, r x → u x → False)
    (htu : ∀ x, t x → u x → False) :
    @Multiset.countP α (fun x => p x ∨ q x ∨ r x ∨ t x ∨ u x)
      (fun x => Classical.propDecidable (p x ∨ q x ∨ r x ∨ t x ∨ u x)) s =
      @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
        @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
          @Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
            @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s +
              @Multiset.countP α u (fun x => Classical.propDecidable (u x)) s := by
  classical
  calc
    @Multiset.countP α (fun x => p x ∨ q x ∨ r x ∨ t x ∨ u x)
      (fun x => Classical.propDecidable (p x ∨ q x ∨ r x ∨ t x ∨ u x)) s =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          @Multiset.countP α (fun x => q x ∨ r x ∨ t x ∨ u x)
            (fun x => Classical.propDecidable (q x ∨ r x ∨ t x ∨ u x)) s := by
      exact multiset_countP_or_eq_add s
        (fun x hp hrest => by
          rcases hrest with hq | hr | ht | hu
          · exact hpq x hp hq
          · exact hpr x hp hr
          · exact hpt x hp ht
          · exact hpu x hp hu)
    _ =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          (@Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
            @Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
              @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s +
                @Multiset.countP α u (fun x => Classical.propDecidable (u x)) s) := by
      rw [multiset_countP_or4_eq_add s hqr hqt hqu hrt hru htu]
    _ =
        @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s +
          @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s +
            @Multiset.countP α r (fun x => Classical.propDecidable (r x)) s +
              @Multiset.countP α t (fun x => Classical.propDecidable (t x)) s +
                @Multiset.countP α u (fun x => Classical.propDecidable (u x)) s := by
      omega

private theorem multiset_countP_congr_iff {α : Type*} {p q : α → Prop}
    (s : Multiset α)
    (h : ∀ x, p x ↔ q x) :
    @Multiset.countP α p (fun x => Classical.propDecidable (p x)) s =
      @Multiset.countP α q (fun x => Classical.propDecidable (q x)) s := by
  classical
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  have hfilter :
      @Multiset.filter α p (fun x => Classical.propDecidable (p x)) s =
        @Multiset.filter α q (fun x => Classical.propDecidable (q x)) s :=
    @Multiset.filter_congr α p q
      (fun x => Classical.propDecidable (p x))
      (fun x => Classical.propDecidable (q x)) s (fun x _hx => h x)
  exact congrArg Multiset.card hfilter

private theorem list_prod_flatMap_replicate {α M : Type*} [CommMonoid M]
    (roots : List α) (count : α → ℕ) (factor : α → M) :
    ((roots.flatMap fun z => List.replicate (count z) (factor z)).prod) =
      (roots.map fun z => (factor z) ^ count z).prod := by
  induction roots with
  | nil =>
      simp
  | cons z zs ih =>
      simp [List.prod_append, ih]

private theorem list_prod_map_flatMap {α β M : Type*} [CommMonoid M]
    (items : α → List β) (factor : β → M) :
    ∀ roots : List α,
      (List.map factor (roots.flatMap items)).prod =
        (roots.map fun z => (items z).map factor |>.prod).prod
  | [] => by simp
  | z :: zs => by
      simp [List.prod_append, list_prod_map_flatMap items factor zs]

private theorem list_prod_flatMap_two {α M : Type*} [CommMonoid M]
    (roots : List α) (f g : α → M) :
    (roots.flatMap fun z => [f z, g z]).prod =
      (roots.map fun z => f z * g z).prod := by
  induction roots with
  | nil => simp
  | cons z zs ih =>
      calc
        ((z :: zs).flatMap fun z => [f z, g z]).prod =
            (f z * g z) * (zs.flatMap fun z => [f z, g z]).prod := by
          simp [mul_assoc]
        _ = (f z * g z) * (zs.map fun z => f z * g z).prod := by
          rw [ih]
        _ = ((z :: zs).map fun z => f z * g z).prod := by
          simp

private theorem list_prod_flatMap_four_pair {α M : Type*} [CommMonoid M]
    (roots : List α) (f g : α → M) :
    (roots.flatMap fun z => [f z, g z, f z, g z]).prod =
      (roots.map fun z => (f z * g z) ^ 2).prod := by
  induction roots with
  | nil => simp
  | cons z zs ih =>
      calc
        ((z :: zs).flatMap fun z => [f z, g z, f z, g z]).prod =
            ((f z * g z) ^ 2) *
              (zs.flatMap fun z => [f z, g z, f z, g z]).prod := by
          simp [pow_two, mul_assoc]
        _ = ((f z * g z) ^ 2) *
              (zs.map fun z => (f z * g z) ^ 2).prod := by
          rw [ih]
        _ = ((z :: zs).map fun z => (f z * g z) ^ 2).prod := by
          simp

private theorem exists_Ioo_not_root_of_ne_zero {P : ℝ[X]} (hP : P ≠ 0)
    {a b : ℝ} (hab : a < b) :
    ∃ x : ℝ, x ∈ Set.Ioo a b ∧ P.eval x ≠ 0 := by
  classical
  let roots : Finset ℝ := P.roots.toFinset
  have hinf : (Set.Ioo a b \ (roots : Set ℝ)).Infinite :=
    (Set.Ioo_infinite hab).sdiff roots.finite_toSet
  rcases hinf.nonempty with ⟨x, hx⟩
  rw [Set.mem_sdiff] at hx
  refine ⟨x, hx.1, ?_⟩
  intro heval
  have hroot : P.IsRoot x := by
    rw [Polynomial.IsRoot.def]
    exact heval
  have hmem_roots : x ∈ P.roots := (Polynomial.mem_roots hP).mpr hroot
  exact hx.2 (by
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact hmem_roots)

private theorem list_count_flatMap {α β : Type*} [BEq β] [LawfulBEq β]
    (roots : List α) (items : α → List β) (target : β) :
    (roots.flatMap items).count target =
      (roots.map fun z => (items z).count target).sum := by
  induction roots with
  | nil =>
      simp
  | cons z zs ih =>
      simp [ih]

private theorem list_count_flatMap_replicate_self {α : Type*}
    [BEq α] [LawfulBEq α] (roots : List α) (count : α → ℕ) (target : α)
    (hnodup : roots.Nodup) :
    (roots.flatMap fun z => List.replicate (count z) z).count target =
      if target ∈ roots then count target else 0 := by
  induction roots with
  | nil =>
      simp
  | cons z zs ih =>
      have hz_not_mem : z ∉ zs := by
        exact (List.nodup_cons.mp hnodup).1
      have hzs_nodup : zs.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      by_cases htarget : target = z
      · subst target
        simp [ih hzs_nodup, hz_not_mem]
      · have hrep : (List.replicate (count z) z).count target = 0 := by
          rw [List.count_eq_zero]
          intro hw
          exact htarget (List.eq_of_mem_replicate hw)
        simp [List.mem_cons, htarget, hrep, ih hzs_nodup]

private theorem list_count_flatMap_replicate_key_of_mem
    {α β : Type*} [BEq β] [LawfulBEq β]
    (roots : List α) (key : α → β) (count : α → ℕ) {target : α}
    (hnodup : (roots.map key).Nodup) (htarget : target ∈ roots) :
    (roots.flatMap fun z => List.replicate (count z) (key z)).count
        (key target) = count target := by
  induction roots with
  | nil =>
      simp at htarget
  | cons z zs ih =>
      have hkey_not_mem : key z ∉ zs.map key := by
        exact (List.nodup_cons.mp hnodup).1
      have htail_nodup : (zs.map key).Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp htarget with hhead | htarget_tail
      · subst z
        have htail_zero :
            (zs.flatMap fun w => List.replicate (count w) (key w)).count
              (key target) = 0 := by
          rw [List.count_eq_zero]
          intro hw
          rcases List.mem_flatMap.mp hw with ⟨w, hw_mem, hw_rep⟩
          have hkey_eq : key target = key w :=
            (List.mem_replicate.mp hw_rep).2
          exact hkey_not_mem (List.mem_map.mpr ⟨w, hw_mem, hkey_eq.symm⟩)
        simp [htail_zero]
      · have hhead_zero : (List.replicate (count z) (key z)).count
            (key target) = 0 := by
          rw [List.count_eq_zero]
          intro hw
          have hkey_eq : key target = key z := List.eq_of_mem_replicate hw
          exact hkey_not_mem (List.mem_map.mpr ⟨target, htarget_tail, hkey_eq⟩)
        have htail := ih htail_nodup htarget_tail
        simp [hhead_zero, htail]

private theorem list_count_flatMap_real_four_orbit
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ =>
      [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)]).count (target : ℂ) =
        2 * params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hneg_ne : (-(s : ℂ)) ≠ (s : ℂ) := by
          intro h
          have hs_eq : (-s : ℝ) = s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hneg_ne, htail]
        omega
      · have htarget_neg_ne : (target : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hreal : target = -s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htarget_s_complex : (target : ℂ) ≠ (s : ℂ) := by
          intro h
          exact htarget_s (Complex.ofReal_injective h)
        have hhead_zero :
            [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)].count
              (target : ℂ) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, Complex.ofReal_inj, List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact htarget_s hmem
          · exact htarget_neg_ne hmem
          · exact htarget_s hmem
          · exact htarget_neg_ne hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)] ++
              (ss.flatMap fun s : ℝ =>
                [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)])).count
              (target : ℂ) =
            2 * (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_real_four_orbit_neg
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ =>
      [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)]).count (-(target : ℂ)) =
        2 * params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hpos_ne_neg : (s : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hs_eq : s = (-s : ℝ) := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hpos_ne_neg, htail]
        omega
      · have htarget_neg_ne : -(target : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hreal : target = s := by
            have h' : (target : ℂ) = (s : ℂ) := by
              simpa using congrArg Neg.neg h
            exact Complex.ofReal_injective h'
          exact htarget_s hreal
        have htarget_pos_ne : -(target : ℂ) ≠ (s : ℂ) := by
          intro h
          have hreal : (-target : ℝ) = s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have hhead_zero :
            [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)].count
              (-(target : ℂ)) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, neg_inj, Complex.ofReal_inj,
            List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact htarget_pos_ne hmem
          · exact htarget_s hmem
          · exact htarget_pos_ne hmem
          · exact htarget_s hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)] ++
              (ss.flatMap fun s : ℝ =>
                [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)])).count
              (-(target : ℂ)) =
            2 * (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_real_two_orbit
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ => [(s : ℂ), -(s : ℂ)]).count
        (target : ℂ) = params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hneg_ne : (-(s : ℂ)) ≠ (s : ℂ) := by
          intro h
          have hs_eq : (-s : ℝ) = s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hneg_ne, htail]
      · have htarget_neg_ne : (target : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hreal : target = -s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htarget_s_complex : (target : ℂ) ≠ (s : ℂ) := by
          intro h
          exact htarget_s (Complex.ofReal_injective h)
        have hhead_zero :
            [(s : ℂ), -(s : ℂ)].count (target : ℂ) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, Complex.ofReal_inj, List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_s hmem
          · exact htarget_neg_ne hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(s : ℂ), -(s : ℂ)] ++
              (ss.flatMap fun s : ℝ => [(s : ℂ), -(s : ℂ)])).count
              (target : ℂ) =
            (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_real_two_orbit_neg
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ => [(s : ℂ), -(s : ℂ)]).count
        (-(target : ℂ)) = params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hpos_ne_neg : (s : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hs_eq : s = (-s : ℝ) := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hpos_ne_neg, htail]
      · have htarget_neg_ne : -(target : ℂ) ≠ -(s : ℂ) := by
          intro h
          have hreal : target = s := by
            have h' : (target : ℂ) = (s : ℂ) := by
              simpa using congrArg Neg.neg h
            exact Complex.ofReal_injective h'
          exact htarget_s hreal
        have htarget_pos_ne : -(target : ℂ) ≠ (s : ℂ) := by
          intro h
          have hreal : (-target : ℝ) = s := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have hhead_zero :
            [(s : ℂ), -(s : ℂ)].count (-(target : ℂ)) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, neg_inj, Complex.ofReal_inj,
            List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_pos_ne hmem
          · exact htarget_s hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(s : ℂ), -(s : ℂ)] ++
              (ss.flatMap fun s : ℝ => [(s : ℂ), -(s : ℂ)])).count
              (-(target : ℂ)) =
            (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_key_real_two_orbit
    {α : Type*} (params : List α) (value : α → ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < value s) (htarget : 0 < target) :
    (params.flatMap fun s : α => [(value s : ℂ), -(value s : ℂ)]).count
        (target : ℂ) = (params.map value).count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < value s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < value t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = value s
      · subst target
        have hneg_ne : (-(value s : ℂ)) ≠ (value s : ℂ) := by
          intro h
          have hs_eq : (-(value s) : ℝ) = value s :=
            Complex.ofReal_injective (by simpa using h)
          linarith
        have htail := ih (target := value s) hss_pos hs_pos
        simp [hneg_ne, htail]
      · have htarget_same_ne : (target : ℂ) ≠ (value s : ℂ) := by
          intro h
          exact htarget_s (Complex.ofReal_injective h)
        have htarget_neg_ne : (target : ℂ) ≠ -(value s : ℂ) := by
          intro h
          have hreal : target = -(value s) := Complex.ofReal_injective (by
            simpa using h)
          linarith
        have hhead_zero :
            [(value s : ℂ), -(value s : ℂ)].count (target : ℂ) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, Complex.ofReal_inj, List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_s hmem
          · exact htarget_neg_ne hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(value s : ℂ), -(value s : ℂ)] ++
              (ss.flatMap fun s : α => [(value s : ℂ), -(value s : ℂ)])).count
              (target : ℂ) =
            (value s :: ss.map value).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : value s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_key_real_two_orbit_neg
    {α : Type*} (params : List α) (value : α → ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < value s) (htarget : 0 < target) :
    (params.flatMap fun s : α => [(value s : ℂ), -(value s : ℂ)]).count
        (-(target : ℂ)) = (params.map value).count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < value s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < value t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = value s
      · subst target
        have hpos_ne_neg : (value s : ℂ) ≠ -(value s : ℂ) := by
          intro h
          have hs_eq : value s = (-(value s) : ℝ) :=
            Complex.ofReal_injective (by simpa using h)
          linarith
        have htail := ih (target := value s) hss_pos hs_pos
        simp [hpos_ne_neg, htail]
      · have htarget_same_ne : -(target : ℂ) ≠ (value s : ℂ) := by
          intro h
          have hreal : (-target : ℝ) = value s :=
            Complex.ofReal_injective (by simpa using h)
          linarith
        have htarget_neg_ne : -(target : ℂ) ≠ -(value s : ℂ) := by
          intro h
          have hreal : target = value s := by
            have h' : (target : ℂ) = (value s : ℂ) := by
              simpa using congrArg Neg.neg h
            exact Complex.ofReal_injective h'
          exact htarget_s hreal
        have hhead_zero :
            [(value s : ℂ), -(value s : ℂ)].count (-(target : ℂ)) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, neg_inj, Complex.ofReal_inj,
            List.not_mem_nil, or_false] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_same_ne hmem
          · exact htarget_s hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([(value s : ℂ), -(value s : ℂ)] ++
              (ss.flatMap fun s : α => [(value s : ℂ), -(value s : ℂ)])).count
              (-(target : ℂ)) =
            (value s :: ss.map value).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : value s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_imaginary_two_orbit
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ =>
      [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))]).count
        (Complex.I * (target : ℂ)) = params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hneg_ne :
            -(Complex.I * (s : ℂ)) ≠ Complex.I * (s : ℂ) := by
          intro h
          have hs_eq : -s = s := by
            have him := congrArg Complex.im h
            simpa using him
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hneg_ne, htail]
      · have htarget_same_ne :
            Complex.I * (target : ℂ) ≠ Complex.I * (s : ℂ) := by
          intro h
          have hreal : target = s := by
            have him := congrArg Complex.im h
            simpa using him
          exact htarget_s hreal
        have htarget_neg_ne :
            Complex.I * (target : ℂ) ≠ -(Complex.I * (s : ℂ)) := by
          intro h
          have hreal : target = -s := by
            have him := congrArg Complex.im h
            simpa using him
          linarith
        have hhead_zero :
            [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))].count
              (Complex.I * (target : ℂ)) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, mul_eq_mul_left_iff, Complex.ofReal_inj,
            Complex.I_ne_zero, or_false, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_s hmem
          · exact htarget_neg_ne hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))] ++
              (ss.flatMap fun s : ℝ =>
                [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))])).count
              (Complex.I * (target : ℂ)) =
            (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

private theorem list_count_flatMap_imaginary_two_orbit_neg
    (params : List ℝ) (target : ℝ)
    (hpos : ∀ s ∈ params, 0 < s) (htarget : 0 < target) :
    (params.flatMap fun s : ℝ =>
      [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))]).count
        (-(Complex.I * (target : ℂ))) = params.count target := by
  induction params generalizing target with
  | nil =>
      simp
  | cons s ss ih =>
      have hs_pos : 0 < s := hpos s (by simp)
      have hss_pos : ∀ t ∈ ss, 0 < t := by
        intro t ht
        exact hpos t (by simp [ht])
      by_cases htarget_s : target = s
      · subst target
        have hpos_ne_neg :
            Complex.I * (s : ℂ) ≠ -(Complex.I * (s : ℂ)) := by
          intro h
          have hs_eq : s = -s := by
            have him := congrArg Complex.im h
            simpa using him
          linarith
        have htail := ih (target := s) hss_pos hs_pos
        simp [hpos_ne_neg, htail]
      · have htarget_same_ne :
            -(Complex.I * (target : ℂ)) ≠ Complex.I * (s : ℂ) := by
          intro h
          have hreal : -target = s := by
            have him := congrArg Complex.im h
            simpa using him
          linarith
        have htarget_neg_ne :
            -(Complex.I * (target : ℂ)) ≠ -(Complex.I * (s : ℂ)) := by
          intro h
          have hreal : target = s := by
            have h' : Complex.I * (target : ℂ) = Complex.I * (s : ℂ) := by
              simpa using congrArg Neg.neg h
            have him := congrArg Complex.im h'
            simpa using him
          exact htarget_s hreal
        have hhead_zero :
            [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))].count
              (-(Complex.I * (target : ℂ))) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, neg_inj, mul_eq_mul_left_iff,
            Complex.ofReal_inj, Complex.I_ne_zero, or_false, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · exact htarget_same_ne hmem
          · exact htarget_s hmem
        have htail := ih (target := target) hss_pos htarget
        change
          ([Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))] ++
              (ss.flatMap fun s : ℝ =>
                [Complex.I * (s : ℂ), -(Complex.I * (s : ℂ))])).count
              (-(Complex.I * (target : ℂ))) =
            (s :: ss).count target
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : s ≠ target := fun h => htarget_s h.symm
        simp [hne]

/-- Even real polynomials evaluate symmetrically after the real-to-complex
coefficient lift.  This is the algebraic root-closure entry point used in
[GSLW19, BlockHam.tex:442]. -/
theorem realPolynomialToComplex_eval_neg_of_hasRealParity_even {A : ℝ[X]}
    (hA : HasRealParity A 0) (z : ℂ) :
    (realPolynomialToComplex A).eval (-z) =
      (realPolynomialToComplex A).eval z := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcoeff : A.coeff n = 0
  · simp [realPolynomialToComplex, hcoeff]
  · have hEven : Even n := Nat.even_iff.mpr (hA n hcoeff)
    rw [hEven.neg_pow z]

/-- Even real polynomials are invariant under the variable substitution
`X ↦ -X` after coefficient extension to `ℂ`.  This is the multiplicity-level
version of the root symmetry in [GSLW19, BlockHam.tex:442]. -/
theorem realPolynomialToComplex_comp_neg_X_of_hasRealParity_even {A : ℝ[X]}
    (hA : HasRealParity A 0) :
    (realPolynomialToComplex A).comp (-X) = realPolynomialToComplex A := by
  ext n
  rw [show (-X : ℂ[X]) = Polynomial.C (-1 : ℂ) * X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases hcoeff : A.coeff n = 0
  · simp [realPolynomialToComplex, hcoeff]
  · have hEven : Even n := Nat.even_iff.mpr (hA n hcoeff)
    simp [realPolynomialToComplex, hEven.neg_one_pow]

/-- Complex roots of an even real polynomial are closed under negation, matching
the source root symmetry in [GSLW19, BlockHam.tex:442]. -/
theorem isRoot_neg_of_hasRealParity_even {A : ℝ[X]} (hA : HasRealParity A 0)
    {z : ℂ} (hz : (realPolynomialToComplex A).IsRoot z) :
    (realPolynomialToComplex A).IsRoot (-z) := by
  rw [Polynomial.IsRoot.def] at hz ⊢
  simpa [realPolynomialToComplex_eval_neg_of_hasRealParity_even hA z] using hz

/-- Multiset-root version of negation closure for even real polynomials.  This
is the roots-layer form needed by the product proof in [GSLW19,
BlockHam.tex:442-456]. -/
theorem mem_roots_neg_of_hasRealParity_even {A : ℝ[X]} (hA : HasRealParity A 0)
    {z : ℂ} (hz : z ∈ (realPolynomialToComplex A).roots) :
    -z ∈ (realPolynomialToComplex A).roots := by
  exact (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hz)).mpr
    (isRoot_neg_of_hasRealParity_even hA (Polynomial.isRoot_of_mem_roots hz))

/-- Root multiplicities of an even real polynomial are invariant under
`z ↦ -z`, matching the paired root accounting in [GSLW19,
BlockHam.tex:442-456]. -/
theorem rootMultiplicity_neg_of_hasRealParity_even {A : ℝ[X]} (hA : HasRealParity A 0)
    (z : ℂ) :
    (realPolynomialToComplex A).rootMultiplicity (-z) =
      (realPolynomialToComplex A).rootMultiplicity z := by
  let P : ℂ[X] := realPolynomialToComplex A
  have hcomp : P.comp (-X) = P := by
    simpa [P] using realPolynomialToComplex_comp_neg_X_of_hasRealParity_even hA
  have hroot :=
    Polynomial.rootMultiplicity_comp_C_mul_X_add_C
      (p := P) (a := (-1 : ℂ)) (b := 0) (c := -z) isUnit_neg_one
  have hcomp' : P.comp (Polynomial.C (-1 : ℂ) * X + Polynomial.C 0) = P := by
    simpa using hcomp
  rw [hcomp'] at hroot
  simpa using hroot

/-- Real-coefficient polynomials commute with complex conjugation under
evaluation. -/
theorem realPolynomialToComplex_eval_conj (A : ℝ[X]) (z : ℂ) :
    (realPolynomialToComplex A).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((realPolynomialToComplex A).eval z) := by
  conv_lhs => rw [← conjP_realPolynomialToComplex A]
  rw [conjP, Polynomial.eval_map]
  rw [Polynomial.eval₂_hom]

/-- Complex roots of a real polynomial are closed under conjugation, matching
the source root symmetry in [GSLW19, BlockHam.tex:442]. -/
theorem isRoot_conj_of_realPolynomialToComplex {A : ℝ[X]} {z : ℂ}
    (hz : (realPolynomialToComplex A).IsRoot z) :
    (realPolynomialToComplex A).IsRoot (starRingEnd ℂ z) := by
  rw [Polynomial.IsRoot.def] at hz ⊢
  rw [realPolynomialToComplex_eval_conj A z, hz]
  simp

/-- Multiset-root version of conjugation closure for real polynomials.  This
is the roots-layer form needed by the product proof in [GSLW19,
BlockHam.tex:442-456]. -/
theorem mem_roots_conj_of_realPolynomialToComplex {A : ℝ[X]} {z : ℂ}
    (hz : z ∈ (realPolynomialToComplex A).roots) :
    starRingEnd ℂ z ∈ (realPolynomialToComplex A).roots := by
  exact (Polynomial.mem_roots (Polynomial.ne_zero_of_mem_roots hz)).mpr
    (isRoot_conj_of_realPolynomialToComplex (Polynomial.isRoot_of_mem_roots hz))

/-- Root multiplicities of a real polynomial are invariant under complex
conjugation, matching the conjugate-root accounting in [GSLW19,
BlockHam.tex:442-456]. -/
theorem rootMultiplicity_conj_of_realPolynomialToComplex (A : ℝ[X]) (z : ℂ) :
    (realPolynomialToComplex A).rootMultiplicity (starRingEnd ℂ z) =
      (realPolynomialToComplex A).rootMultiplicity z := by
  let P : ℂ[X] := realPolynomialToComplex A
  have hroot :=
    Polynomial.eq_rootMultiplicity_map
      (p := P) (f := starRingEnd ℂ) (RingHom.injective (starRingEnd ℂ)) z
  have hmap : P.map (starRingEnd ℂ) = P := by
    simpa [P, conjP] using conjP_realPolynomialToComplex A
  rw [hmap] at hroot
  simpa [P] using hroot.symm

/-- Extract one point on each side of an interior point from a neighborhood
eventuality.  This elementary real-analysis lemma is used below to turn odd
root multiplicity into a sign change on the interval. -/
theorem exists_left_right_of_eventually_nhds {s : ℝ} {p : ℝ → Prop}
    (hp : ∀ᶠ x in nhds s, p x) (hl : -1 < s) (hr : s < 1) :
    ∃ x y, x ∈ Set.Icc (-1 : ℝ) 1 ∧ y ∈ Set.Icc (-1 : ℝ) 1 ∧
      x < s ∧ s < y ∧ p x ∧ p y := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨ε, hε, hball⟩
  let δ : ℝ := min (ε / 2) (min ((s + 1) / 2) ((1 - s) / 2))
  have hε2 : 0 < ε / 2 := by linarith
  have hleft : 0 < (s + 1) / 2 := by linarith
  have hright : 0 < (1 - s) / 2 := by linarith
  have hδpos : 0 < δ := by
    exact lt_min hε2 (lt_min hleft hright)
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδpos
  have hδ_le_ε2 : δ ≤ ε / 2 := min_le_left _ _
  have hδ_lt_ε : δ < ε := by linarith
  have hδ_le_left : δ ≤ (s + 1) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_le_right : δ ≤ (1 - s) / 2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨s - δ, s + δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · linarith
  · linarith
  · apply hball
    rw [Real.dist_eq]
    have hsub : s - δ - s = -δ := by ring
    rw [hsub, abs_of_nonpos (neg_nonpos.mpr hδ_nonneg)]
    linarith
  · apply hball
    rw [Real.dist_eq]
    have hsub : s + δ - s = δ := by ring
    rw [hsub, abs_of_nonneg hδ_nonneg]
    exact hδ_lt_ε

/-- Interior real roots of an interval-nonnegative real polynomial have even
multiplicity.  This is the sign-change step behind the source root
classification in [GSLW19, BlockHam.tex:442-456]. -/
theorem rootMultiplicity_even_of_nonnegativeOnUnitInterval {P : ℝ[X]} {s : ℝ}
    (hP0 : P ≠ 0) (hs : s ∈ Set.Ioo (-1 : ℝ) 1)
    (hnonneg : NonnegativeOnUnitInterval P) :
    Even (P.rootMultiplicity s) := by
  by_contra hnot
  have hodd : Odd (P.rootMultiplicity s) := Nat.not_even_iff_odd.mp hnot
  rcases Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 s with
    ⟨q, hfactor, hq_not_dvd⟩
  let m : ℕ := P.rootMultiplicity s
  have hm_odd : Odd m := by simpa [m] using hodd
  have hfactor_m : P = (X - C s) ^ m * q := by
    simpa [m] using hfactor
  have hq_ne : q.eval s ≠ 0 := by
    intro hq_zero
    have hq_root : q.IsRoot s := by
      rw [Polynomial.IsRoot.def]
      exact hq_zero
    exact hq_not_dvd ((Polynomial.dvd_iff_isRoot).mpr hq_root)
  have h_eval :
      ∀ x : ℝ, P.eval x = (x - s) ^ m * q.eval x := by
    intro x
    calc
      P.eval x = (((X - C s) ^ m * q).eval x) := by
        rw [hfactor_m]
      _ = (x - s) ^ P.rootMultiplicity s * q.eval x := by
        simp [m, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub]
  rcases lt_or_gt_of_ne hq_ne with hq_neg | hq_pos
  · have hq_eventually : ∀ᶠ x in nhds s, q.eval x < 0 := by
      have hpre :
          (fun x : ℝ => q.eval x) ⁻¹' Set.Iio 0 ∈ nhds s :=
        (Polynomial.continuous q).continuousAt.preimage_mem_nhds
          (Iio_mem_nhds hq_neg)
      simpa [Filter.Eventually, Set.preimage, Set.Iio] using hpre
    rcases exists_left_right_of_eventually_nhds hq_eventually hs.1 hs.2 with
      ⟨_x, y, _hxI, hyI, _hxs, hsy, _hxq, hyq⟩
    have hysub : 0 < y - s := sub_pos.mpr hsy
    have hpow_pos : 0 < (y - s) ^ m :=
      pow_pos hysub _
    have hPy_neg : P.eval y < 0 := by
      rw [h_eval y]
      exact mul_neg_of_pos_of_neg hpow_pos hyq
    have hPy_nonneg := hnonneg y hyI
    linarith
  · have hq_eventually : ∀ᶠ x in nhds s, 0 < q.eval x := by
      have hpre :
          (fun x : ℝ => q.eval x) ⁻¹' Set.Ioi 0 ∈ nhds s :=
        (Polynomial.continuous q).continuousAt.preimage_mem_nhds
          (Ioi_mem_nhds hq_pos)
      simpa [Filter.Eventually, Set.preimage, Set.Ioi] using hpre
    rcases exists_left_right_of_eventually_nhds hq_eventually hs.1 hs.2 with
      ⟨x, _y, hxI, _hyI, hxs, _hsy, hxq, _hyq⟩
    have hxsub : x - s < 0 := sub_neg.mpr hxs
    have hpow_neg : (x - s) ^ m < 0 :=
      (Odd.pow_neg_iff hm_odd).mpr hxsub
    have hPx_neg : P.eval x < 0 := by
      rw [h_eval x]
      exact mul_neg_of_neg_of_pos hpow_neg hxq
    have hPx_nonneg := hnonneg x hxI
    linarith

/-- The zero-root multiplicity of an even real polynomial is even.  This
accounts for the `S_0` root class in [GSLW19, BlockHam.tex:442-452]. -/
theorem rootMultiplicity_zero_even_of_hasRealParity_even {P : ℝ[X]}
    (hP : HasRealParity P 0) :
    Even (P.rootMultiplicity 0) := by
  by_cases hzero : P = 0
  · simp [hzero]
  · rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
    have hcoeff : P.coeff P.natTrailingDegree ≠ 0 :=
      (Polynomial.coeff_natTrailingDegree_ne_zero).mpr hzero
    exact Nat.even_iff.mpr (hP P.natTrailingDegree hcoeff)

/-- Root-class facts extracted from the source hypotheses in the proof of the
interval-square decomposition [GSLW19, BlockHam.tex:442-456].

The eventual product construction consumes this package rather than re-proving
sign-change or symmetry facts at each root class. -/
abbrev SourceRootClassFacts (A : ℝ[X]) :=
  Complement.Interval.Roots.SourceRootClassFacts A

/-- Source hypotheses imply the root-class facts used in the Gilyén product
construction [GSLW19, BlockHam.tex:442-456]. -/
theorem SourceHypotheses.rootClassFacts {A : ℝ[X]} {k : ℕ}
    (hA : SourceHypotheses A k) : SourceRootClassFacts A where
  zero_multiplicity_even := rootMultiplicity_zero_even_of_hasRealParity_even hA.even
  interior_multiplicity_even := by
    intro s hs
    by_cases hzero : A = 0
    · simp [hzero]
    · exact rootMultiplicity_even_of_nonnegativeOnUnitInterval hzero hs hA.nonnegative
  complex_ofReal_multiplicity := by
    intro s
    exact (realPolynomialToComplex_rootMultiplicity_ofReal A s).symm
  complex_neg_multiplicity := rootMultiplicity_neg_of_hasRealParity_even hA.even
  complex_conj_multiplicity := rootMultiplicity_conj_of_realPolynomialToComplex A

namespace SourceRootClassFacts

/-- Zero-root evenness transported to the complexified polynomial. -/
theorem complex_zero_multiplicity_even {A : ℝ[X]} (facts : SourceRootClassFacts A) :
    Even ((realPolynomialToComplex A).rootMultiplicity (0 : ℂ)) := by
  change Even ((realPolynomialToComplex A).rootMultiplicity ((0 : ℝ) : ℂ))
  rw [facts.complex_ofReal_multiplicity 0]
  exact facts.zero_multiplicity_even

/-- Interior real-root evenness transported to the complexified polynomial. -/
theorem complex_ofReal_interior_multiplicity_even {A : ℝ[X]}
    (facts : SourceRootClassFacts A) {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    Even ((realPolynomialToComplex A).rootMultiplicity (s : ℂ)) := by
  rw [facts.complex_ofReal_multiplicity s]
  exact facts.interior_multiplicity_even s hs

end SourceRootClassFacts

/-- Complex root product factorization of a real polynomial after coefficient
extension.  This is the Mathlib splitting bridge used before grouping the
source root classes in [GSLW19, BlockHam.tex:450-456]. -/
theorem realPolynomialToComplex_eq_leadingCoeff_mul_roots (A : ℝ[X]) :
    realPolynomialToComplex A =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        ((realPolynomialToComplex A).roots.map fun z => X - C z).prod := by
  exact (IsAlgClosed.splits (realPolynomialToComplex A)).eq_prod_roots

/-- Source-root data before choosing one representative from each root class.
It combines the complex product factorization with the sign/parity facts that
justify the source's root grouping [GSLW19, BlockHam.tex:442-456]. -/
abbrev SourceRootProductData (A : ℝ[X]) :=
  Complement.Interval.Product.SourceRootProductData A

/-- Source hypotheses produce the root-product data used immediately before
the representative-grouping step in [GSLW19, BlockHam.tex:442-456]. -/
noncomputable def SourceHypotheses.rootProductData {A : ℝ[X]} {k : ℕ}
    (hA : SourceHypotheses A k) : SourceRootProductData A where
  roots := (realPolynomialToComplex A).roots
  product_eq := realPolynomialToComplex_eq_leadingCoeff_mul_roots A
  facts := hA.rootClassFacts

/-- Root-product form indexed by distinct roots and their multiplicities.  This
is the product expression that the source root-class proof groups into zero,
real, imaginary, and complex quartet factors [GSLW19, BlockHam.tex:450-456]. -/
theorem SourceRootProductData.product_eq_toFinset_roots {A : ℝ[X]}
    (data : SourceRootProductData A)
    (hroots : data.roots = (realPolynomialToComplex A).roots) :
    realPolynomialToComplex A =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        data.roots.toFinset.prod
          (fun z => ((X : ℂ[X]) - Polynomial.C z) ^
            (realPolynomialToComplex A).rootMultiplicity z) := by
  calc
    realPolynomialToComplex A =
        Polynomial.C (realPolynomialToComplex A).leadingCoeff *
          ((realPolynomialToComplex A).roots.map fun z => (X : ℂ[X]) - Polynomial.C z).prod := by
            simpa [hroots] using data.product_eq
    _ = Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        (realPolynomialToComplex A).roots.toFinset.prod
          (fun z => ((X : ℂ[X]) - Polynomial.C z) ^
            (realPolynomialToComplex A).rootMultiplicity z) := by
      rw [Polynomial.prod_multiset_root_eq_finset_root
        (p := realPolynomialToComplex A)]
    _ = Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        data.roots.toFinset.prod
          (fun z => ((X : ℂ[X]) - Polynomial.C z) ^
            (realPolynomialToComplex A).rootMultiplicity z) := by
      simp [hroots]

/-- The distinct-root product form for the canonical root-product data extracted
from `SourceHypotheses` [GSLW19, BlockHam.tex:450-456]. -/
theorem SourceHypotheses.rootProductData_product_eq_toFinset_roots
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    realPolynomialToComplex A =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        (hA.rootProductData).roots.toFinset.prod
          (fun z => ((X : ℂ[X]) - Polynomial.C z) ^
            (realPolynomialToComplex A).rootMultiplicity z) :=
  hA.rootProductData.product_eq_toFinset_roots rfl

/-- In the canonical source root multiset, multiplicity in the multiset is
exactly polynomial root multiplicity.  This is the counting bridge used in the
source root-class degree argument [GSLW19, BlockHam.tex:469-479]. -/
theorem SourceHypotheses.rootProductData_count_eq_rootMultiplicity
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) (z : ℂ) :
    (hA.rootProductData).roots.count z =
      (realPolynomialToComplex A).rootMultiplicity z := by
  rw [SourceHypotheses.rootProductData]
  exact Polynomial.count_roots (p := realPolynomialToComplex A) (a := z)

/-- The canonical source root multiset has cardinality at most `2k`, because
`deg(A) <= 2k` in [GSLW19, BlockHam.tex:436-438]. -/
theorem SourceHypotheses.rootProductData_roots_card_le_two_mul
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).roots.card ≤ 2 * k := by
  have hdeg : (realPolynomialToComplex A).natDegree ≤ 2 * k := by
    simpa [realPolynomialToComplex_natDegree] using hA.degree_le
  simpa [SourceHypotheses.rootProductData] using
    (Polynomial.card_roots' (realPolynomialToComplex A)).trans hdeg

/-- The four-element orbit `z, -z, z^*, -z^*` used for non-real, non-imaginary
root classes in the source grouping step [GSLW19, BlockHam.tex:450-456]. -/
def complexRootOrbit (z : ℂ) : List ℂ :=
  [z, -z, starRingEnd ℂ z, -(starRingEnd ℂ z)]

/-- The quartet orbit is symmetric. -/
theorem mem_complexRootOrbit_symm {z w : ℂ}
    (hw : w ∈ complexRootOrbit z) :
    z ∈ complexRootOrbit w := by
  simp only [complexRootOrbit, List.mem_cons] at hw ⊢
  rcases hw with rfl | rfl | rfl | hw
  · simp
  · simp
  · simp
  · rcases hw with rfl | hfalse
    · simp
    · cases hfalse

private theorem complex_pair_eq_of_eq {a b c d : ℝ}
    (h : (a : ℂ) + Complex.I * (b : ℂ) =
      (c : ℂ) + Complex.I * (d : ℂ)) :
    (a, b) = (c, d) := by
  have hre : a = c := by
    simpa using congrArg Complex.re h
  have him : b = d := by
    simpa using congrArg Complex.im h
  exact Prod.ext hre him

private theorem complex_firstQuadrant_ne_neg {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    (a : ℂ) + Complex.I * (b : ℂ) ≠
      -((c : ℂ) + Complex.I * (d : ℂ)) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

private theorem complex_firstQuadrant_ne_conj {a b c d : ℝ}
    (hb : 0 < b) (hd : 0 < d) :
    (a : ℂ) + Complex.I * (b : ℂ) ≠
      starRingEnd ℂ ((c : ℂ) + Complex.I * (d : ℂ)) := by
  intro h
  have him := congrArg Complex.im h
  simp [Complex.conj_I, Complex.conj_ofReal] at him
  linarith

private theorem complex_firstQuadrant_ne_neg_conj {a b c d : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    (a : ℂ) + Complex.I * (b : ℂ) ≠
      -(starRingEnd ℂ ((c : ℂ) + Complex.I * (d : ℂ))) := by
  intro h
  have hre := congrArg Complex.re h
  simp [Complex.conj_I, Complex.conj_ofReal] at hre
  linarith

private theorem list_count_flatMap_complex_orbit
    (params : List (ℝ × ℝ)) (a b : ℝ)
    (hpos : ∀ z ∈ params, 0 < z.1 ∧ 0 < z.2)
    (ha : 0 < a) (hb : 0 < b) :
    (params.flatMap fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
        ((a : ℂ) + Complex.I * (b : ℂ)) = params.count (a, b) := by
  induction params with
  | nil =>
      simp
  | cons z zs ih =>
      have hzpos : 0 < z.1 ∧ 0 < z.2 := hpos z (by simp)
      have hzspos : ∀ w ∈ zs, 0 < w.1 ∧ 0 < w.2 := by
        intro w hw
        exact hpos w (by simp [hw])
      by_cases htarget_z : (a, b) = z
      · subst z
        have hneg_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              -((a : ℂ) + Complex.I * (b : ℂ)) :=
          complex_firstQuadrant_ne_neg ha ha
        have hconj_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)) :=
          complex_firstQuadrant_ne_conj hb hb
        have hneg_conj_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              -(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) :=
          complex_firstQuadrant_ne_neg_conj ha ha
        let w : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        have hrest_zero :
            [ -w, starRingEnd ℂ w, -(starRingEnd ℂ w) ].count w = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem | hmem
          · exact hneg_ne (by simpa [w] using hmem)
          · exact hconj_ne (by simpa [w] using hmem)
          · exact hneg_conj_ne (by simpa [w] using hmem)
        have hhead_one :
            (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ))).count
              ((a : ℂ) + Complex.I * (b : ℂ)) = 1 := by
          change (w :: [-w, starRingEnd ℂ w, -(starRingEnd ℂ w)]).count w = 1
          simp [hrest_zero]
        have htail := ih hzspos
        change
          (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              ((a : ℂ) + Complex.I * (b : ℂ)) =
            ((a, b) :: zs).count (a, b)
        rw [List.count_append, hhead_one, htail]
        simp [Nat.add_comm]
      · have hsame_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              (z.1 : ℂ) + Complex.I * (z.2 : ℂ) := by
          intro h
          exact htarget_z (complex_pair_eq_of_eq h)
        have hneg_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              -((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) :=
          complex_firstQuadrant_ne_neg ha hzpos.1
        have hconj_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) :=
          complex_firstQuadrant_ne_conj hb hzpos.2
        have hneg_conj_ne :
            (a : ℂ) + Complex.I * (b : ℂ) ≠
              -(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) :=
          complex_firstQuadrant_ne_neg_conj ha hzpos.1
        have hhead_zero :
            (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
              ((a : ℂ) + Complex.I * (b : ℂ)) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact hsame_ne hmem
          · exact hneg_ne hmem
          · exact hconj_ne hmem
          · rcases hmem with hmem | hfalse
            · exact hneg_conj_ne hmem
            · cases hfalse
        have htail := ih hzspos
        change
          (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              ((a : ℂ) + Complex.I * (b : ℂ)) =
            (z :: zs).count (a, b)
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : z ≠ (a, b) := fun h => htarget_z h.symm
        simp [hne]

private theorem list_count_flatMap_complex_orbit_neg
    (params : List (ℝ × ℝ)) (a b : ℝ)
    (hpos : ∀ z ∈ params, 0 < z.1 ∧ 0 < z.2)
    (ha : 0 < a) (hb : 0 < b) :
    (params.flatMap fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
        (-((a : ℂ) + Complex.I * (b : ℂ))) = params.count (a, b) := by
  induction params with
  | nil =>
      simp
  | cons z zs ih =>
      have hzpos : 0 < z.1 ∧ 0 < z.2 := hpos z (by simp)
      have hzspos : ∀ w ∈ zs, 0 < w.1 ∧ 0 < w.2 := by
        intro w hw
        exact hpos w (by simp [hw])
      by_cases htarget_z : (a, b) = z
      · subst z
        let w : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        have hneg_ne : w ≠ -w := complex_firstQuadrant_ne_neg ha ha
        have hconj_ne : w ≠ starRingEnd ℂ w :=
          complex_firstQuadrant_ne_conj hb hb
        have hneg_conj_ne : w ≠ -(starRingEnd ℂ w) :=
          complex_firstQuadrant_ne_neg_conj ha ha
        have htail_zero :
            [starRingEnd ℂ w, -(starRingEnd ℂ w)].count (-w) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem
          · exact hneg_conj_ne (by simpa [w] using congrArg Neg.neg hmem)
          · rcases hmem with hmem | hfalse
            · exact hconj_ne (by simpa [w] using congrArg Neg.neg hmem)
            · cases hfalse
        have hhead_one :
            (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ))).count
              (-((a : ℂ) + Complex.I * (b : ℂ))) = 1 := by
          change (w :: -w :: [starRingEnd ℂ w, -(starRingEnd ℂ w)]).count (-w) = 1
          rw [List.count_cons]
          have hfirst : (w == -w) = false := by
            exact beq_false_of_ne hneg_ne
          simp [hfirst, htail_zero]
        have htail := ih hzspos
        change
          (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (-((a : ℂ) + Complex.I * (b : ℂ))) =
            ((a, b) :: zs).count (a, b)
        rw [List.count_append, hhead_one, htail]
        simp [Nat.add_comm]
      · let target : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
        have hsame_neg_ne : -target ≠ w := by
          intro h
          exact (complex_firstQuadrant_ne_neg hzpos.1 ha) (by simpa [target, w] using h.symm)
        have hneg_ne : -target ≠ -w := by
          intro h
          have htarget_eq : (a, b) = z :=
            complex_pair_eq_of_eq (by simpa [target, w] using congrArg Neg.neg h)
          exact htarget_z htarget_eq
        have hconj_ne : -target ≠ starRingEnd ℂ w := by
          intro h
          exact (complex_firstQuadrant_ne_neg_conj ha hzpos.1)
            (by simpa [target, w] using congrArg Neg.neg h)
        have hneg_conj_ne : -target ≠ -(starRingEnd ℂ w) := by
          intro h
          exact (complex_firstQuadrant_ne_conj hb hzpos.2)
            (by simpa [target, w] using congrArg Neg.neg h)
        have hhead_zero :
            (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
              (-((a : ℂ) + Complex.I * (b : ℂ))) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact hsame_neg_ne hmem
          · exact hneg_ne hmem
          · exact hconj_ne hmem
          · rcases hmem with hmem | hfalse
            · exact hneg_conj_ne hmem
            · cases hfalse
        have htail := ih hzspos
        change
          (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (-((a : ℂ) + Complex.I * (b : ℂ))) =
            (z :: zs).count (a, b)
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : z ≠ (a, b) := fun h => htarget_z h.symm
        simp [hne]

private theorem list_count_flatMap_complex_orbit_conj
    (params : List (ℝ × ℝ)) (a b : ℝ)
    (hpos : ∀ z ∈ params, 0 < z.1 ∧ 0 < z.2)
    (ha : 0 < a) (hb : 0 < b) :
    (params.flatMap fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
        (starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) =
      params.count (a, b) := by
  induction params with
  | nil =>
      simp
  | cons z zs ih =>
      have hzpos : 0 < z.1 ∧ 0 < z.2 := hpos z (by simp)
      have hzspos : ∀ w ∈ zs, 0 < w.1 ∧ 0 < w.2 := by
        intro w hw
        exact hpos w (by simp [hw])
      by_cases htarget_z : (a, b) = z
      · subst z
        let w : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        have hneg_ne : w ≠ -w := complex_firstQuadrant_ne_neg ha ha
        have hconj_ne : w ≠ starRingEnd ℂ w :=
          complex_firstQuadrant_ne_conj hb hb
        have hneg_conj_ne : w ≠ -(starRingEnd ℂ w) :=
          complex_firstQuadrant_ne_neg_conj ha ha
        have hconj_neg_conj_ne :
            starRingEnd ℂ w ≠ -(starRingEnd ℂ w) := by
          intro h
          exact hneg_ne (by
            have h' := congrArg (starRingEnd ℂ) h
            simpa [w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hhead_one :
            (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ))).count
              (starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) = 1 := by
          change
            (w :: -w :: starRingEnd ℂ w :: [-(starRingEnd ℂ w)]).count
              (starRingEnd ℂ w) = 1
          rw [List.count_cons]
          have hfirst : (w == starRingEnd ℂ w) = false := by
            exact beq_false_of_ne hconj_ne
          rw [List.count_cons]
          have hsecond : (-w == starRingEnd ℂ w) = false := by
            exact beq_false_of_ne (by
              intro h
              exact hneg_conj_ne (by
                have h' := congrArg Neg.neg h
                simpa [w] using h'))
          simp [hfirst, hsecond, hconj_neg_conj_ne]
        have htail := ih hzspos
        change
          (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) =
            ((a, b) :: zs).count (a, b)
        rw [List.count_append, hhead_one, htail]
        simp [Nat.add_comm]
      · let target : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
        have hsame_ne : starRingEnd ℂ target ≠ w := by
          intro h
          exact (complex_firstQuadrant_ne_conj hb hzpos.2)
            (by
              have h' := congrArg (starRingEnd ℂ) h
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hneg_ne : starRingEnd ℂ target ≠ -w := by
          intro h
          exact (complex_firstQuadrant_ne_neg_conj ha hzpos.1)
            (by
              have h' := congrArg (starRingEnd ℂ) h
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hconj_ne : starRingEnd ℂ target ≠ starRingEnd ℂ w := by
          intro h
          have htarget_eq : (a, b) = z :=
            complex_pair_eq_of_eq
              (by
                have h' := congrArg (starRingEnd ℂ) h
                simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
          exact htarget_z htarget_eq
        have hneg_conj_ne : starRingEnd ℂ target ≠ -(starRingEnd ℂ w) := by
          intro h
          exact (complex_firstQuadrant_ne_neg ha hzpos.1)
            (by
              have h' := congrArg (starRingEnd ℂ) h
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hhead_zero :
            (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
              (starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact hsame_ne hmem
          · exact hneg_ne hmem
          · exact hconj_ne hmem
          · rcases hmem with hmem | hfalse
            · exact hneg_conj_ne hmem
            · cases hfalse
        have htail := ih hzspos
        change
          (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ))) =
            (z :: zs).count (a, b)
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : z ≠ (a, b) := fun h => htarget_z h.symm
        simp [hne]

private theorem list_count_flatMap_complex_orbit_neg_conj
    (params : List (ℝ × ℝ)) (a b : ℝ)
    (hpos : ∀ z ∈ params, 0 < z.1 ∧ 0 < z.2)
    (ha : 0 < a) (hb : 0 < b) :
    (params.flatMap fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
        (-(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)))) =
      params.count (a, b) := by
  induction params with
  | nil =>
      simp
  | cons z zs ih =>
      have hzpos : 0 < z.1 ∧ 0 < z.2 := hpos z (by simp)
      have hzspos : ∀ w ∈ zs, 0 < w.1 ∧ 0 < w.2 := by
        intro w hw
        exact hpos w (by simp [hw])
      by_cases htarget_z : (a, b) = z
      · subst z
        let w : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        have hneg_ne : w ≠ -w := complex_firstQuadrant_ne_neg ha ha
        have hconj_ne : w ≠ starRingEnd ℂ w :=
          complex_firstQuadrant_ne_conj hb hb
        have hneg_conj_ne : w ≠ -(starRingEnd ℂ w) :=
          complex_firstQuadrant_ne_neg_conj ha ha
        have hconj_neg_conj_ne :
            starRingEnd ℂ w ≠ -(starRingEnd ℂ w) := by
          intro h
          exact hneg_ne (by
            have h' := congrArg (starRingEnd ℂ) h
            simpa [w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hhead_one :
            (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ))).count
              (-(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)))) = 1 := by
          change
            (w :: -w :: starRingEnd ℂ w :: [-(starRingEnd ℂ w)]).count
              (-(starRingEnd ℂ w)) = 1
          rw [List.count_cons]
          have hfirst : (w == -(starRingEnd ℂ w)) = false := by
            exact beq_false_of_ne hneg_conj_ne
          rw [List.count_cons]
          have hsecond : (-w == -(starRingEnd ℂ w)) = false := by
            exact beq_false_of_ne (by
              intro h
              exact hconj_ne (by
                have h' := congrArg Neg.neg h
                simpa [w] using h'))
          rw [List.count_cons]
          have hthird : (starRingEnd ℂ w == -(starRingEnd ℂ w)) = false := by
            exact beq_false_of_ne hconj_neg_conj_ne
          simp [hfirst, hsecond, hthird]
        have htail := ih hzspos
        change
          (complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (-(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)))) =
            ((a, b) :: zs).count (a, b)
        rw [List.count_append, hhead_one, htail]
        simp [Nat.add_comm]
      · let target : ℂ := (a : ℂ) + Complex.I * (b : ℂ)
        let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
        have hsame_ne : -(starRingEnd ℂ target) ≠ w := by
          intro h
          exact (complex_firstQuadrant_ne_neg_conj ha hzpos.1)
            (by
              have h' := congrArg Neg.neg (congrArg (starRingEnd ℂ) h)
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hneg_ne : -(starRingEnd ℂ target) ≠ -w := by
          intro h
          exact (complex_firstQuadrant_ne_conj hb hzpos.2)
            (by
              have h' := congrArg (starRingEnd ℂ) (congrArg Neg.neg h)
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hconj_ne : -(starRingEnd ℂ target) ≠ starRingEnd ℂ w := by
          intro h
          exact (complex_firstQuadrant_ne_neg ha hzpos.1)
            (by
              have h' := congrArg Neg.neg (congrArg (starRingEnd ℂ) h)
              simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
        have hneg_conj_ne : -(starRingEnd ℂ target) ≠ -(starRingEnd ℂ w) := by
          intro h
          have htarget_eq : (a, b) = z :=
            complex_pair_eq_of_eq
              (by
                have h' := congrArg (starRingEnd ℂ) (congrArg Neg.neg h)
                simpa [target, w, Complex.conj_I, Complex.conj_ofReal] using h')
          exact htarget_z htarget_eq
        have hhead_zero :
            (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).count
              (-(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)))) = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hmem
          rcases hmem with hmem | hmem | hmem | hmem
          · exact hsame_ne hmem
          · exact hneg_ne hmem
          · exact hconj_ne hmem
          · rcases hmem with hmem | hfalse
            · exact hneg_conj_ne hmem
            · cases hfalse
        have htail := ih hzspos
        change
          (complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ++
              (zs.flatMap fun z : ℝ × ℝ =>
                complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
              (-(starRingEnd ℂ ((a : ℂ) + Complex.I * (b : ℂ)))) =
            (z :: zs).count (a, b)
        rw [List.count_append, hhead_zero, htail]
        rw [List.count_cons]
        have hne : z ≠ (a, b) := fun h => htarget_z h.symm
        simp [hne]

/-- Evenness and real coefficients make the source root set closed under the
quartet orbit used in [GSLW19, BlockHam.tex:450-456]. -/
theorem mem_roots_of_mem_complexRootOrbit {A : ℝ[X]} (hA : HasRealParity A 0)
    {z w : ℂ} (hz : z ∈ (realPolynomialToComplex A).roots)
    (hw : w ∈ complexRootOrbit z) :
    w ∈ (realPolynomialToComplex A).roots := by
  simp only [complexRootOrbit, List.mem_cons] at hw
  rcases hw with rfl | rfl | rfl | hw
  · exact hz
  · exact mem_roots_neg_of_hasRealParity_even hA hz
  · exact mem_roots_conj_of_realPolynomialToComplex hz
  · rcases hw with rfl | hfalse
    · exact mem_roots_neg_of_hasRealParity_even hA
        (mem_roots_conj_of_realPolynomialToComplex hz)
    · cases hfalse

/-- Multiplicities are constant on the quartet orbit used by the source root
classification [GSLW19, BlockHam.tex:450-456]. -/
theorem rootMultiplicity_eq_of_mem_complexRootOrbit {A : ℝ[X]}
    (hA : HasRealParity A 0) {z w : ℂ} (hw : w ∈ complexRootOrbit z) :
    (realPolynomialToComplex A).rootMultiplicity w =
      (realPolynomialToComplex A).rootMultiplicity z := by
  simp only [complexRootOrbit, List.mem_cons] at hw
  rcases hw with rfl | rfl | rfl | hw
  · rfl
  · exact rootMultiplicity_neg_of_hasRealParity_even hA z
  · exact rootMultiplicity_conj_of_realPolynomialToComplex A z
  · rcases hw with rfl | hfalse
    · calc
      (realPolynomialToComplex A).rootMultiplicity (-(starRingEnd ℂ z)) =
          (realPolynomialToComplex A).rootMultiplicity (starRingEnd ℂ z) :=
        rootMultiplicity_neg_of_hasRealParity_even hA (starRingEnd ℂ z)
      _ = (realPolynomialToComplex A).rootMultiplicity z :=
        rootMultiplicity_conj_of_realPolynomialToComplex A z
    · cases hfalse

/-- The canonical source root-product data is closed under the quartet orbit
used by the source root-class grouping [GSLW19, BlockHam.tex:450-456]. -/
theorem SourceHypotheses.mem_rootProductData_roots_of_mem_complexRootOrbit
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    {z w : ℂ} (hz : z ∈ (hA.rootProductData).roots)
    (hw : w ∈ complexRootOrbit z) :
    w ∈ (hA.rootProductData).roots :=
  mem_roots_of_mem_complexRootOrbit hA.even hz hw

/-- In the canonical source root-product data, multiplicities are constant on
the quartet orbit [GSLW19, BlockHam.tex:450-456]. -/
theorem SourceHypotheses.rootProductData_rootMultiplicity_eq_of_mem_complexRootOrbit
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z w : ℂ}
    (hw : w ∈ complexRootOrbit z) :
    (realPolynomialToComplex A).rootMultiplicity w =
      (realPolynomialToComplex A).rootMultiplicity z :=
  rootMultiplicity_eq_of_mem_complexRootOrbit hA.even hw

/-- In the canonical source root multiset, actual multiset counts are constant
on the quartet orbit.  This is the multiset-count form of the source root
symmetry used in [GSLW19, BlockHam.tex:450-456,469-479]. -/
theorem SourceHypotheses.rootProductData_count_eq_of_mem_complexRootOrbit
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z w : ℂ}
    (hw : w ∈ complexRootOrbit z) :
    (hA.rootProductData).roots.count w =
      (hA.rootProductData).roots.count z := by
  rw [hA.rootProductData_count_eq_rootMultiplicity w,
    hA.rootProductData_count_eq_rootMultiplicity z,
    hA.rootProductData_rootMultiplicity_eq_of_mem_complexRootOrbit hw]

/-- The canonical root multiset is invariant under sign change, because the
source polynomial is even [GSLW19, BlockHam.tex:442-456]. -/
theorem SourceHypotheses.rootProductData_roots_map_neg
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).roots.map (fun z : ℂ => -z) =
      (hA.rootProductData).roots := by
  classical
  ext z
  calc
    ((hA.rootProductData).roots.map (fun w : ℂ => -w)).count z =
        (hA.rootProductData).roots.count (-z) := by
      simpa using
        (Multiset.count_map_eq_count' (fun w : ℂ => -w)
          (hA.rootProductData).roots
          (by
            intro a b hab
            simpa using congrArg Neg.neg hab)
          (-z))
    _ = (hA.rootProductData).roots.count z := by
      exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
        (z := z) (w := -z) (by simp [complexRootOrbit])

/-- The canonical root multiset is invariant under complex conjugation, because
the source polynomial has real coefficients [GSLW19, BlockHam.tex:442-456]. -/
theorem SourceHypotheses.rootProductData_roots_map_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).roots.map (fun z : ℂ => starRingEnd ℂ z) =
      (hA.rootProductData).roots := by
  classical
  ext z
  calc
    ((hA.rootProductData).roots.map (fun w : ℂ => starRingEnd ℂ w)).count z =
        (hA.rootProductData).roots.count (starRingEnd ℂ z) := by
      simpa using
        (Multiset.count_map_eq_count' (fun w : ℂ => starRingEnd ℂ w)
          (hA.rootProductData).roots
          (starRingEnd ℂ).injective
          (starRingEnd ℂ z))
    _ = (hA.rootProductData).roots.count z := by
      exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
        (z := z) (w := starRingEnd ℂ z) (by simp [complexRootOrbit])

/-- The canonical root multiset is invariant under the composition
`z ↦ -conj z`, the fourth member of the source complex quartet. -/
theorem SourceHypotheses.rootProductData_roots_map_neg_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).roots.map (fun z : ℂ => -(starRingEnd ℂ z)) =
      (hA.rootProductData).roots := by
  classical
  ext z
  calc
    ((hA.rootProductData).roots.map (fun w : ℂ => -(starRingEnd ℂ w))).count z =
        (hA.rootProductData).roots.count (-(starRingEnd ℂ z)) := by
      simpa using
        (Multiset.count_map_eq_count' (fun w : ℂ => -(starRingEnd ℂ w))
          (hA.rootProductData).roots
          (by
            intro a b hab
            have hstar : starRingEnd ℂ a = starRingEnd ℂ b := by
              simpa using congrArg Neg.neg hab
            exact (starRingEnd ℂ).injective hstar)
          (-(starRingEnd ℂ z)))
    _ = (hA.rootProductData).roots.count z := by
      exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
        (z := z) (w := -(starRingEnd ℂ z)) (by simp [complexRootOrbit])

/-! Root-class predicates for the representative-selection step in
[GSLW19, BlockHam.tex:450-456].  They are deliberately phrased on complex
roots, while later source factors consume the real parameters. -/

/-- Positive real roots strictly inside the unit interval.  Their multiplicity
is even, so the eventual source product uses half as many squared-pair factors. -/
def IsPositiveInteriorRealRootRepresentative (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 < z.re ∧ z.re < 1

/-- Positive real roots at or outside the unit interval, including endpoint
roots at `1`.  The source factor is `s^2 - x^2`. -/
def IsPositiveOutsideRealRootRepresentative (z : ℂ) : Prop :=
  z.im = 0 ∧ 1 ≤ z.re

/-- Pure imaginary roots with positive imaginary part.  The source factor is
`x^2 + r^2`. -/
def IsPositiveImaginaryRootRepresentative (z : ℂ) : Prop :=
  z.re = 0 ∧ 0 < z.im

/-- Non-real, non-imaginary roots are represented by the first-quadrant member
of the quartet `z, -z, z^*, -z^*`. -/
def IsFirstQuadrantComplexRootRepresentative (z : ℂ) : Prop :=
  0 < z.re ∧ 0 < z.im

/-- A source root-class representative is either zero, a positive real root
inside the interval, a positive real root at/outside the interval, a positive
imaginary root, or a first-quadrant non-real root. -/
def IsSourceRootClassRepresentative (z : ℂ) : Prop :=
  z = 0 ∨
    IsPositiveInteriorRealRootRepresentative z ∨
    IsPositiveOutsideRealRootRepresentative z ∨
    IsPositiveImaginaryRootRepresentative z ∨
    IsFirstQuadrantComplexRootRepresentative z

/-- The full real-inside-the-interval root class, including both signs of the
positive representative [GSLW19, BlockHam.tex:445,452-454]. -/
def IsInteriorRealRootClass (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 < |z.re| ∧ |z.re| < 1

/-- The full real outside/end-point root class, including both signs of the
positive representative [GSLW19, BlockHam.tex:446,453-460]. -/
def IsOutsideRealRootClass (z : ℂ) : Prop :=
  z.im = 0 ∧ 1 ≤ |z.re|

/-- The full pure-imaginary root class, including both signs of the positive
imaginary representative [GSLW19, BlockHam.tex:447,455,461]. -/
def IsImaginaryRootClass (z : ℂ) : Prop :=
  z.re = 0 ∧ 0 < |z.im|

/-- The genuine complex quartet root class, represented in the source by its
first-quadrant member [GSLW19, BlockHam.tex:448,455-456,462-466]. -/
def IsComplexQuartetRootClass (z : ℂ) : Prop :=
  z.re ≠ 0 ∧ z.im ≠ 0

/-- Full source root-class partition predicate: zero, signed real inside,
signed real outside, signed pure imaginary, or genuine complex. -/
def IsSourceRootClassMember (z : ℂ) : Prop :=
  z = 0 ∨ IsInteriorRealRootClass z ∨ IsOutsideRealRootClass z ∨
    IsImaginaryRootClass z ∨ IsComplexQuartetRootClass z

/-- The five source root classes cover every complex number.  The source uses
this partition on the complex root multiset before selecting representatives
[GSLW19, BlockHam.tex:442-448]. -/
theorem sourceRootClassMember_exhaustive (z : ℂ) :
    IsSourceRootClassMember z := by
  classical
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  · by_cases him : z.im = 0
    · have hre_ne : z.re ≠ 0 := by
        intro hre
        apply hz0
        apply Complex.ext <;> simp [hre, him]
      by_cases hlt : |z.re| < 1
      · exact Or.inr (Or.inl ⟨him, abs_pos.mpr hre_ne, hlt⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨him, le_of_not_gt hlt⟩))
    · by_cases hre : z.re = 0
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hre, abs_pos.mpr him⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hre, him⟩)))

/-- Counting negative interior representatives is the same as counting
positive interior representatives. -/
theorem SourceHypotheses.countP_neg_positiveInterior_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z => IsPositiveInteriorRealRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative (-z))) (hA.rootProductData).roots =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z => IsPositiveInteriorRealRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative (-z))) (hA.rootProductData).roots =
        @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => -z)) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_neg]

/-- A signed interior real root is either the positive representative or the
negative of one [GSLW19, BlockHam.tex:445]. -/
theorem isInteriorRealRootClass_iff_positive_or_negative {z : ℂ} :
    IsInteriorRealRootClass z ↔
      IsPositiveInteriorRealRootRepresentative z ∨
        IsPositiveInteriorRealRootRepresentative (-z) := by
  constructor
  · intro h
    rcases h with ⟨him, h_abs_pos, h_abs_lt⟩
    have hre_ne : z.re ≠ 0 := abs_pos.mp h_abs_pos
    rcases lt_or_gt_of_ne hre_ne.symm with hre_pos | hre_neg
    · left
      constructor
      · exact him
      constructor
      · exact hre_pos
      · simpa [abs_of_pos hre_pos] using h_abs_lt
    · right
      have hbounds := abs_lt.mp h_abs_lt
      constructor
      · simp [him]
      constructor
      · simpa using neg_pos.mpr hre_neg
      · have hlt : -z.re < 1 := by linarith [hbounds.1]
        simpa using hlt
  · rintro (hpos | hneg)
    · exact ⟨hpos.1, by simpa [abs_of_pos hpos.2.1] using hpos.2.1,
        by simpa [abs_of_pos hpos.2.1] using hpos.2.2⟩
    · have hre_neg : z.re < 0 := by
        have hpos_neg : 0 < -z.re := by simpa using hneg.2.1
        linarith
      have him : z.im = 0 := by
        simpa using hneg.1
      exact ⟨him, by simpa [abs_of_neg hre_neg] using neg_pos.mpr hre_neg,
        by
          have hlt : -z.re < 1 := hneg.2.2
          simpa [abs_of_neg hre_neg] using hlt⟩

/-- Counting all signed interior real roots is twice the count of positive
interior representatives.  This is the multiplicity accounting behind the
source's paired factors for roots in `(-1,1)` [GSLW19,
BlockHam.tex:445,452-454]. -/
theorem SourceHypotheses.countP_interiorRealRootClass_eq_two_mul_countP_positiveInterior
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ IsInteriorRealRootClass
        (fun z => Classical.propDecidable (IsInteriorRealRootClass z))
        (hA.rootProductData).roots =
      2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  let roots := (hA.rootProductData).roots
  let pos :=
    @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
      (fun z => Classical.propDecidable
        (IsPositiveInteriorRealRootRepresentative z)) roots
  calc
    @Multiset.countP ℂ IsInteriorRealRootClass
        (fun z => Classical.propDecidable (IsInteriorRealRootClass z)) roots =
        @Multiset.countP ℂ (fun z =>
          IsPositiveInteriorRealRootRepresentative z ∨
            IsPositiveInteriorRealRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z ∨
              IsPositiveInteriorRealRootRepresentative (-z))) roots := by
      exact multiset_countP_congr_iff roots
        (fun z => isInteriorRealRootClass_iff_positive_or_negative (z := z))
    _ =
        @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) roots +
        @Multiset.countP ℂ (fun z => IsPositiveInteriorRealRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative (-z))) roots := by
      exact multiset_countP_or_eq_add roots
        (fun z hz hneg => by
          have hpos : 0 < z.re := hz.2.1
          have hnegpos : 0 < -z.re := by simpa using hneg.2.1
          linarith)
    _ = pos + pos := by
      simp [pos, roots, hA.countP_neg_positiveInterior_eq_countP]
    _ = 2 * pos := by omega

/-- Counting negative outside-real representatives is the same as counting
positive outside-real representatives. -/
theorem SourceHypotheses.countP_neg_positiveOutside_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z => IsPositiveOutsideRealRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative (-z))) (hA.rootProductData).roots =
      @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z => IsPositiveOutsideRealRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative (-z))) (hA.rootProductData).roots =
        @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => -z)) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_neg]

/-- A signed outside real root is either the positive representative or the
negative of one [GSLW19, BlockHam.tex:446,453-460]. -/
theorem isOutsideRealRootClass_iff_positive_or_negative {z : ℂ} :
    IsOutsideRealRootClass z ↔
      IsPositiveOutsideRealRootRepresentative z ∨
        IsPositiveOutsideRealRootRepresentative (-z) := by
  constructor
  · intro h
    rcases h with ⟨him, h_abs⟩
    rcases le_or_gt 0 z.re with hre_nonneg | hre_neg
    · left
      constructor
      · exact him
      · simpa [abs_of_nonneg hre_nonneg] using h_abs
    · right
      constructor
      · simp [him]
      · have hle : 1 ≤ -z.re := by
          simpa [abs_of_neg hre_neg] using h_abs
        simpa using hle
  · rintro (hpos | hneg)
    · have hre_nonneg : 0 ≤ z.re := by linarith [hpos.2]
      exact ⟨hpos.1, by simpa [abs_of_nonneg hre_nonneg] using hpos.2⟩
    · have hre_neg : z.re < 0 := by
        have hle : 1 ≤ -z.re := by simpa using hneg.2
        linarith
      have him : z.im = 0 := by
        simpa using hneg.1
      exact ⟨him, by
        have hle : 1 ≤ -z.re := by simpa using hneg.2
        simpa [abs_of_neg hre_neg] using hle⟩

/-- Counting all signed outside real roots is twice the count of positive
outside representatives [GSLW19, BlockHam.tex:446,453-460]. -/
theorem SourceHypotheses.countP_outsideRealRootClass_eq_two_mul_countP_positiveOutside
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ IsOutsideRealRootClass
        (fun z => Classical.propDecidable (IsOutsideRealRootClass z))
        (hA.rootProductData).roots =
      2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  let roots := (hA.rootProductData).roots
  let pos :=
    @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
      (fun z => Classical.propDecidable
        (IsPositiveOutsideRealRootRepresentative z)) roots
  calc
    @Multiset.countP ℂ IsOutsideRealRootClass
        (fun z => Classical.propDecidable (IsOutsideRealRootClass z)) roots =
        @Multiset.countP ℂ (fun z =>
          IsPositiveOutsideRealRootRepresentative z ∨
            IsPositiveOutsideRealRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z ∨
              IsPositiveOutsideRealRootRepresentative (-z))) roots := by
      exact multiset_countP_congr_iff roots
        (fun z => isOutsideRealRootClass_iff_positive_or_negative (z := z))
    _ =
        @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) roots +
        @Multiset.countP ℂ (fun z => IsPositiveOutsideRealRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative (-z))) roots := by
      exact multiset_countP_or_eq_add roots
        (fun z hz hneg => by
          have hpos : 1 ≤ z.re := hz.2
          have hnegpos : 1 ≤ -z.re := by simpa using hneg.2
          linarith)
    _ = pos + pos := by
      simp [pos, roots, hA.countP_neg_positiveOutside_eq_countP]
    _ = 2 * pos := by omega

/-- Counting negative pure-imaginary representatives is the same as counting
positive pure-imaginary representatives. -/
theorem SourceHypotheses.countP_neg_positiveImaginary_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z => IsPositiveImaginaryRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative (-z))) (hA.rootProductData).roots =
      @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z => IsPositiveImaginaryRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative (-z))) (hA.rootProductData).roots =
        @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => -z)) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_neg]

/-- A signed pure-imaginary root is either the positive representative or the
negative of one [GSLW19, BlockHam.tex:447,455,461]. -/
theorem isImaginaryRootClass_iff_positive_or_negative {z : ℂ} :
    IsImaginaryRootClass z ↔
      IsPositiveImaginaryRootRepresentative z ∨
        IsPositiveImaginaryRootRepresentative (-z) := by
  constructor
  · intro h
    rcases h with ⟨hre, h_abs_pos⟩
    have him_ne : z.im ≠ 0 := abs_pos.mp h_abs_pos
    rcases lt_or_gt_of_ne him_ne.symm with him_pos | him_neg
    · left
      exact ⟨hre, him_pos⟩
    · right
      constructor
      · simp [hre]
      · simpa using neg_pos.mpr him_neg
  · rintro (hpos | hneg)
    · exact ⟨hpos.1, by simpa [abs_of_pos hpos.2] using hpos.2⟩
    · have him_neg : z.im < 0 := by
        have hpos_neg : 0 < -z.im := by simpa using hneg.2
        linarith
      have hre : z.re = 0 := by
        simpa using hneg.1
      exact ⟨hre, by simpa [abs_of_neg him_neg] using neg_pos.mpr him_neg⟩

/-- Counting all signed pure-imaginary roots is twice the count of positive
imaginary representatives [GSLW19, BlockHam.tex:447,455,461]. -/
theorem SourceHypotheses.countP_imaginaryRootClass_eq_two_mul_countP_positiveImaginary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ IsImaginaryRootClass
        (fun z => Classical.propDecidable (IsImaginaryRootClass z))
        (hA.rootProductData).roots =
      2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  let roots := (hA.rootProductData).roots
  let pos :=
    @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
      (fun z => Classical.propDecidable
        (IsPositiveImaginaryRootRepresentative z)) roots
  calc
    @Multiset.countP ℂ IsImaginaryRootClass
        (fun z => Classical.propDecidable (IsImaginaryRootClass z)) roots =
        @Multiset.countP ℂ (fun z =>
          IsPositiveImaginaryRootRepresentative z ∨
            IsPositiveImaginaryRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z ∨
              IsPositiveImaginaryRootRepresentative (-z))) roots := by
      exact multiset_countP_congr_iff roots
        (fun z => isImaginaryRootClass_iff_positive_or_negative (z := z))
    _ =
        @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) roots +
        @Multiset.countP ℂ (fun z => IsPositiveImaginaryRootRepresentative (-z))
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative (-z))) roots := by
      exact multiset_countP_or_eq_add roots
        (fun z hz hneg => by
          have hpos : 0 < z.im := hz.2
          have hnegpos : 0 < -z.im := by simpa using hneg.2
          linarith)
    _ = pos + pos := by
      simp [pos, roots, hA.countP_neg_positiveImaginary_eq_countP]
    _ = 2 * pos := by omega

/-- Counting the negative member of each first-quadrant quartet is the same as
counting the first-quadrant representative. -/
theorem SourceHypotheses.countP_neg_firstQuadrant_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z => IsFirstQuadrantComplexRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (-z))) (hA.rootProductData).roots =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z => IsFirstQuadrantComplexRootRepresentative (-z))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (-z))) (hA.rootProductData).roots =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => -z)) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_neg]

/-- Counting the conjugate member of each first-quadrant quartet is the same
as counting the first-quadrant representative. -/
theorem SourceHypotheses.countP_conj_firstQuadrant_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z => IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z)))
          (hA.rootProductData).roots =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z => IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z)))
          (hA.rootProductData).roots =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => starRingEnd ℂ z)) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_conj]

/-- Counting the negative-conjugate member of each first-quadrant quartet is
the same as counting the first-quadrant representative. -/
theorem SourceHypotheses.countP_neg_conj_firstQuadrant_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ (fun z =>
        IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z))))
          (hA.rootProductData).roots =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  calc
    @Multiset.countP ℂ (fun z =>
        IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z))))
          (hA.rootProductData).roots =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z))
          ((hA.rootProductData).roots.map (fun z : ℂ => -(starRingEnd ℂ z))) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
    _ =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
      rw [hA.rootProductData_roots_map_neg_conj]

/-- A genuine complex root class is represented by exactly one of the four
transforms `z`, `-z`, `z^*`, `-z^*` in the first quadrant [GSLW19,
BlockHam.tex:448,455-456,462-466]. -/
theorem isComplexQuartetRootClass_iff_quadrant_or_transforms {z : ℂ} :
    IsComplexQuartetRootClass z ↔
      IsFirstQuadrantComplexRootRepresentative z ∨
        IsFirstQuadrantComplexRootRepresentative (-z) ∨
          IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z) ∨
            IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)) := by
  constructor
  · intro h
    rcases h with ⟨hre_ne, him_ne⟩
    rcases lt_or_gt_of_ne hre_ne.symm with hre_pos | hre_neg
    · rcases lt_or_gt_of_ne him_ne.symm with him_pos | him_neg
      · exact Or.inl ⟨hre_pos, him_pos⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hre_pos, by simpa using neg_pos.mpr him_neg⟩))
    · rcases lt_or_gt_of_ne him_ne.symm with him_pos | him_neg
      · exact Or.inr (Or.inr (Or.inr ⟨by simpa using neg_pos.mpr hre_neg,
          by simpa using him_pos⟩))
      · exact Or.inr (Or.inl ⟨by simpa using neg_pos.mpr hre_neg,
          by simpa using neg_pos.mpr him_neg⟩)
  · rintro (hquad | hneg | hconj | hnegconj)
    · exact ⟨ne_of_gt hquad.1, ne_of_gt hquad.2⟩
    · have hre_neg : z.re < 0 := by
        have hpos : 0 < -z.re := by simpa using hneg.1
        linarith
      have him_neg : z.im < 0 := by
        have hpos : 0 < -z.im := by simpa using hneg.2
        linarith
      exact ⟨ne_of_lt hre_neg, ne_of_lt him_neg⟩
    · have him_neg : z.im < 0 := by
        have hpos : 0 < -z.im := by simpa using hconj.2
        linarith
      have hre_pos : 0 < z.re := by simpa using hconj.1
      exact ⟨ne_of_gt hre_pos, ne_of_lt him_neg⟩
    · have hre_neg : z.re < 0 := by
        have hpos : 0 < -z.re := by simpa using hnegconj.1
        linarith
      have him_pos : 0 < z.im := by simpa using hnegconj.2
      exact ⟨ne_of_lt hre_neg, ne_of_gt him_pos⟩

/-- Counting the full complex quartet root class is four times the count of
first-quadrant representatives [GSLW19, BlockHam.tex:448,455-456,462-466]. -/
theorem SourceHypotheses.countP_complexQuartetRootClass_eq_four_mul_countP_firstQuadrant
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    @Multiset.countP ℂ IsComplexQuartetRootClass
        (fun z => Classical.propDecidable (IsComplexQuartetRootClass z))
        (hA.rootProductData).roots =
      4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  let roots := (hA.rootProductData).roots
  let pos :=
    @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
      (fun z => Classical.propDecidable
        (IsFirstQuadrantComplexRootRepresentative z)) roots
  calc
    @Multiset.countP ℂ IsComplexQuartetRootClass
        (fun z => Classical.propDecidable (IsComplexQuartetRootClass z)) roots =
        @Multiset.countP ℂ (fun z =>
          IsFirstQuadrantComplexRootRepresentative z ∨
            IsFirstQuadrantComplexRootRepresentative (-z) ∨
              IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z) ∨
                IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z ∨
              IsFirstQuadrantComplexRootRepresentative (-z) ∨
                IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z) ∨
                  IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))) roots := by
      exact multiset_countP_congr_iff roots
        (fun z => isComplexQuartetRootClass_iff_quadrant_or_transforms (z := z))
    _ =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) roots +
          @Multiset.countP ℂ (fun z => IsFirstQuadrantComplexRootRepresentative (-z))
            (fun z => Classical.propDecidable
              (IsFirstQuadrantComplexRootRepresentative (-z))) roots +
            @Multiset.countP ℂ (fun z =>
              IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z))
              (fun z => Classical.propDecidable
                (IsFirstQuadrantComplexRootRepresentative (starRingEnd ℂ z))) roots +
              @Multiset.countP ℂ (fun z =>
                IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))
                (fun z => Classical.propDecidable
                  (IsFirstQuadrantComplexRootRepresentative (-(starRingEnd ℂ z)))) roots := by
      exact multiset_countP_or4_eq_add roots
        (fun z hz hneg => by
          have hre : 0 < z.re := hz.1
          have hneg_re : 0 < -z.re := by simpa using hneg.1
          linarith)
        (fun z hz hconj => by
          have him : 0 < z.im := hz.2
          have hconj_im : 0 < -z.im := by simpa using hconj.2
          linarith)
        (fun z hz hnegconj => by
          have hre : 0 < z.re := hz.1
          have hnegconj_re : 0 < -z.re := by simpa using hnegconj.1
          linarith)
        (fun z hneg hconj => by
          have hneg_re : 0 < -z.re := by simpa using hneg.1
          have hconj_re : 0 < z.re := by simpa using hconj.1
          linarith)
        (fun z hneg hnegconj => by
          have hneg_im : 0 < -z.im := by simpa using hneg.2
          have hnegconj_im : 0 < z.im := by simpa using hnegconj.2
          linarith)
        (fun z hconj hnegconj => by
          have hconj_re : 0 < z.re := by simpa using hconj.1
          have hnegconj_re : 0 < -z.re := by simpa using hnegconj.1
          linarith)
    _ = pos + pos + pos + pos := by
      simp [pos, roots, hA.countP_neg_firstQuadrant_eq_countP,
        hA.countP_conj_firstQuadrant_eq_countP,
        hA.countP_neg_conj_firstQuadrant_eq_countP]
    _ = 4 * pos := by omega

/-- Zero is disjoint from positive interior real representatives
[GSLW19, BlockHam.tex:444-445]. -/
theorem not_zero_and_positiveInterior {z : ℂ} :
    ¬(z = 0 ∧ IsPositiveInteriorRealRootRepresentative z) := by
  rintro ⟨rfl, hpos⟩
  exact (lt_irrefl (0 : ℝ)) hpos.2.1

/-- Zero is disjoint from outside positive real representatives
[GSLW19, BlockHam.tex:444,446]. -/
theorem not_zero_and_positiveOutside {z : ℂ} :
    ¬(z = 0 ∧ IsPositiveOutsideRealRootRepresentative z) := by
  rintro ⟨rfl, houtside⟩
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa using houtside.2
  linarith

/-- Zero is disjoint from positive imaginary representatives
[GSLW19, BlockHam.tex:444,447]. -/
theorem not_zero_and_positiveImaginary {z : ℂ} :
    ¬(z = 0 ∧ IsPositiveImaginaryRootRepresentative z) := by
  rintro ⟨rfl, himag⟩
  exact (lt_irrefl (0 : ℝ)) himag.2

/-- Zero is disjoint from first-quadrant representatives
[GSLW19, BlockHam.tex:444,448]. -/
theorem not_zero_and_firstQuadrant {z : ℂ} :
    ¬(z = 0 ∧ IsFirstQuadrantComplexRootRepresentative z) := by
  rintro ⟨rfl, hquad⟩
  exact (lt_irrefl (0 : ℝ)) hquad.1

/-- Interior positive real representatives and outside positive real
representatives are disjoint root classes [GSLW19, BlockHam.tex:445-446]. -/
theorem not_positiveInterior_and_positiveOutside {z : ℂ} :
    ¬(IsPositiveInteriorRealRootRepresentative z ∧
      IsPositiveOutsideRealRootRepresentative z) := by
  rintro ⟨hinterior, houtside⟩
  linarith [hinterior.2.2, houtside.2]

/-- Positive real representatives are disjoint from positive imaginary
representatives [GSLW19, BlockHam.tex:445-447]. -/
theorem not_positiveInterior_and_positiveImaginary {z : ℂ} :
    ¬(IsPositiveInteriorRealRootRepresentative z ∧
      IsPositiveImaginaryRootRepresentative z) := by
  rintro ⟨hreal, himag⟩
  linarith [hreal.2.1, himag.1]

/-- Outside positive real representatives are disjoint from positive imaginary
representatives [GSLW19, BlockHam.tex:446-447]. -/
theorem not_positiveOutside_and_positiveImaginary {z : ℂ} :
    ¬(IsPositiveOutsideRealRootRepresentative z ∧
      IsPositiveImaginaryRootRepresentative z) := by
  rintro ⟨hreal, himag⟩
  linarith [hreal.2, himag.1]

/-- Real-root representatives are disjoint from first-quadrant representatives
[GSLW19, BlockHam.tex:445-448]. -/
theorem not_positiveInterior_and_firstQuadrant {z : ℂ} :
    ¬(IsPositiveInteriorRealRootRepresentative z ∧
      IsFirstQuadrantComplexRootRepresentative z) := by
  rintro ⟨hreal, hquad⟩
  linarith [hreal.1, hquad.2]

/-- Outside real-root representatives are disjoint from first-quadrant
representatives [GSLW19, BlockHam.tex:446-448]. -/
theorem not_positiveOutside_and_firstQuadrant {z : ℂ} :
    ¬(IsPositiveOutsideRealRootRepresentative z ∧
      IsFirstQuadrantComplexRootRepresentative z) := by
  rintro ⟨hreal, hquad⟩
  linarith [hreal.1, hquad.2]

/-- Positive imaginary representatives are disjoint from first-quadrant
representatives [GSLW19, BlockHam.tex:447-448]. -/
theorem not_positiveImaginary_and_firstQuadrant {z : ℂ} :
    ¬(IsPositiveImaginaryRootRepresentative z ∧
      IsFirstQuadrantComplexRootRepresentative z) := by
  rintro ⟨himag, hquad⟩
  linarith [himag.1, hquad.1]

private theorem list_count_positiveInterior_re_filter
    [DecidablePred IsPositiveInteriorRealRootRepresentative]
    (l : List ℂ) {s : ℝ} (hs : 0 < s ∧ s < 1) :
    List.count s ((l.filter IsPositiveInteriorRealRootRepresentative).map
      fun z => z.re) =
      l.count (s : ℂ) := by
  classical
  induction l with
  | nil =>
      simp
  | cons z zs ih =>
      by_cases hp : IsPositiveInteriorRealRootRepresentative z
      · by_cases hz : z = (s : ℂ)
        · subst hz
          simp [hp, ih]
        · have hzre : z.re ≠ s := by
            intro h
            apply hz
            apply Complex.ext
            · exact h
            · simpa using hp.1
          simp [hp, hz, hzre, ih]
      · have hz : z ≠ (s : ℂ) := by
          intro h
          apply hp
          rw [h]
          exact ⟨by simp, hs⟩
        simp [hp, hz, ih]

private theorem list_count_positiveOutside_re_filter
    [DecidablePred IsPositiveOutsideRealRootRepresentative]
    (l : List ℂ) {s : ℝ} (hs : 1 ≤ s) :
    List.count s ((l.filter IsPositiveOutsideRealRootRepresentative).map
      fun z => z.re) =
      l.count (s : ℂ) := by
  classical
  induction l with
  | nil =>
      simp
  | cons z zs ih =>
      by_cases hp : IsPositiveOutsideRealRootRepresentative z
      · by_cases hz : z = (s : ℂ)
        · subst hz
          simp [hp, ih]
        · have hzre : z.re ≠ s := by
            intro h
            apply hz
            apply Complex.ext
            · exact h
            · simpa using hp.1
          simp [hp, hz, hzre, ih]
      · have hz : z ≠ (s : ℂ) := by
          intro h
          apply hp
          rw [h]
          exact ⟨by simp, hs⟩
        simp [hp, hz, ih]

private theorem list_count_positiveImaginary_im_filter
    [DecidablePred IsPositiveImaginaryRootRepresentative]
    (l : List ℂ) {r : ℝ} (hr : 0 < r) :
    List.count r ((l.filter IsPositiveImaginaryRootRepresentative).map
      fun z => z.im) =
      l.count (Complex.I * (r : ℂ)) := by
  classical
  induction l with
  | nil =>
      simp
  | cons z zs ih =>
      by_cases hp : IsPositiveImaginaryRootRepresentative z
      · by_cases hz : z = Complex.I * (r : ℂ)
        · subst hz
          simp [hp, ih]
        · have hzim : z.im ≠ r := by
            intro h
            apply hz
            apply Complex.ext
            · simpa using hp.1
            · rw [h]
              simp
          simp [hp, hz, hzim, ih]
      · have hz : z ≠ Complex.I * (r : ℂ) := by
          intro h
          apply hp
          rw [h]
          constructor
          · simp
          · simpa using hr
        simp [hp, hz, ih]

private theorem list_count_firstQuadrant_reim_filter
    [DecidablePred IsFirstQuadrantComplexRootRepresentative]
    (l : List ℂ) {z : ℝ × ℝ} (hzpos : 0 < z.1 ∧ 0 < z.2) :
    List.count z ((l.filter IsFirstQuadrantComplexRootRepresentative).map
      fun w => (w.re, w.im)) =
      l.count ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := by
  classical
  induction l with
  | nil =>
      simp
  | cons w ws ih =>
      by_cases hp : IsFirstQuadrantComplexRootRepresentative w
      · by_cases hw : w = (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
        · subst hw
          simp [hp, ih]
        · have hwreim : (w.re, w.im) ≠ z := by
            intro h
            apply hw
            apply Complex.ext
            · simpa using congrArg Prod.fst h
            · simpa using congrArg Prod.snd h
          simp [hp, hw, hwreim, ih]
      · have hw : w ≠ (z.1 : ℂ) + Complex.I * (z.2 : ℂ) := by
          intro h
          apply hp
          rw [h]
          simpa [IsFirstQuadrantComplexRootRepresentative] using hzpos
        simp [hp, hw, ih]

/-- Every complex number has a representative in its source quartet orbit.  This
is the elementary geometry behind the representative choice in [GSLW19,
BlockHam.tex:450-456]. -/
theorem exists_sourceRootClassRepresentative_mem_orbit (z : ℂ) :
    ∃ w ∈ complexRootOrbit z, IsSourceRootClassRepresentative w := by
  by_cases hz0 : z = 0
  · refine ⟨0, ?_, Or.inl rfl⟩
    subst hz0
    simp [complexRootOrbit]
  · by_cases him : z.im = 0
    · by_cases hre_pos : 0 < z.re
      · refine ⟨z, ?_, ?_⟩
        · simp [complexRootOrbit]
        · by_cases hlt : z.re < 1
          · exact Or.inr (Or.inl ⟨him, hre_pos, hlt⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨him, le_of_not_gt hlt⟩))
      · have hre_neg : z.re < 0 := by
          have hre_ne : z.re ≠ 0 := by
            intro hzero
            apply hz0
            apply Complex.ext <;> simp [hzero, him]
          exact lt_of_le_of_ne (le_of_not_gt hre_pos) hre_ne
        refine ⟨-z, ?_, ?_⟩
        · simp [complexRootOrbit]
        · have him_neg : (-z).im = 0 := by simp [him]
          have hre_neg_pos : 0 < (-z).re := by simpa using neg_pos.mpr hre_neg
          by_cases hlt : (-z).re < 1
          · exact Or.inr (Or.inl ⟨him_neg, hre_neg_pos, hlt⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨him_neg, le_of_not_gt hlt⟩))
    · by_cases hre_zero : z.re = 0
      · by_cases him_pos : 0 < z.im
        · refine ⟨z, ?_, ?_⟩
          · simp [complexRootOrbit]
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hre_zero, him_pos⟩)))
        · have him_neg : z.im < 0 := by
            exact lt_of_le_of_ne (le_of_not_gt him_pos) him
          refine ⟨-z, ?_, ?_⟩
          · simp [complexRootOrbit]
          · have hre_neg_zero : (-z).re = 0 := by simp [hre_zero]
            have him_neg_pos : 0 < (-z).im := by simpa using neg_pos.mpr him_neg
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hre_neg_zero, him_neg_pos⟩)))
      · by_cases hre_pos : 0 < z.re
        · by_cases him_pos : 0 < z.im
          · refine ⟨z, ?_, ?_⟩
            · simp [complexRootOrbit]
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hre_pos, him_pos⟩)))
          · have him_neg : z.im < 0 := by
              exact lt_of_le_of_ne (le_of_not_gt him_pos) him
            refine ⟨starRingEnd ℂ z, ?_, ?_⟩
            · simp [complexRootOrbit]
            · have him_conj_pos : 0 < (starRingEnd ℂ z).im := by
                simp [him_neg]
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simpa using hre_pos, him_conj_pos⟩)))
        · have hre_neg : z.re < 0 := by
            exact lt_of_le_of_ne (le_of_not_gt hre_pos) hre_zero
          by_cases him_pos : 0 < z.im
          · refine ⟨-(starRingEnd ℂ z), ?_, ?_⟩
            · simp [complexRootOrbit]
            · have hre_rep_pos : 0 < (-(starRingEnd ℂ z)).re := by
                simpa using neg_pos.mpr hre_neg
              have him_rep_pos : 0 < (-(starRingEnd ℂ z)).im := by
                simpa using him_pos
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hre_rep_pos, him_rep_pos⟩)))
          · have him_neg : z.im < 0 := by
              exact lt_of_le_of_ne (le_of_not_gt him_pos) him
            refine ⟨-z, ?_, ?_⟩
            · simp [complexRootOrbit]
            · have hre_rep_pos : 0 < (-z).re := by simpa using neg_pos.mpr hre_neg
              have him_rep_pos : 0 < (-z).im := by simpa using neg_pos.mpr him_neg
              exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hre_rep_pos, him_rep_pos⟩)))

/-- Every root in the canonical source root-product data has a representative,
still in that root multiset, of one of the source classes [GSLW19,
BlockHam.tex:450-456]. -/
theorem SourceHypotheses.exists_sourceRepresentative_mem_rootProductData
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    {z : ℂ} (hz : z ∈ (hA.rootProductData).roots) :
    ∃ w, w ∈ (hA.rootProductData).roots ∧
      w ∈ complexRootOrbit z ∧ IsSourceRootClassRepresentative w := by
  rcases exists_sourceRootClassRepresentative_mem_orbit z with ⟨w, hw_orbit, hw_rep⟩
  exact ⟨w, hA.mem_rootProductData_roots_of_mem_complexRootOrbit hz hw_orbit,
    hw_orbit, hw_rep⟩

namespace SourceRootProductData

/-- Positive interior real root representatives selected from the complex root
multiset [GSLW19, BlockHam.tex:450-456]. -/
noncomputable def positiveInteriorRealRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ := by
  classical
  exact ((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
    (fun z => z.re)).dedup

/-- Positive endpoint/outside real root representatives selected from the
complex root multiset [GSLW19, BlockHam.tex:450-456]. -/
noncomputable def positiveOutsideRealRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ := by
  classical
  exact ((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
    (fun z => z.re)).dedup

/-- Positive imaginary root representatives selected from the complex root
multiset [GSLW19, BlockHam.tex:450-456]. -/
noncomputable def positiveImaginaryRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ := by
  classical
  exact ((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
    (fun z => z.im)).dedup

/-- First-quadrant complex representatives selected from the complex root
multiset [GSLW19, BlockHam.tex:450-456]. -/
noncomputable def firstQuadrantComplexRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) : List (ℝ × ℝ) := by
  classical
  exact ((data.roots.toList.filter IsFirstQuadrantComplexRootRepresentative).map
    (fun z => (z.re, z.im))).dedup

/-- First-quadrant complex representatives kept as complex roots.  This
auxiliary list is used only for root-multiplicity counting; source factors
still consume the pair-valued `firstQuadrantComplexRootValues`. -/
noncomputable def firstQuadrantComplexRootRepresentatives {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℂ := by
  classical
  exact data.roots.toList.dedup.filter IsFirstQuadrantComplexRootRepresentative

/-- The positive-interior representative list has no duplicate parameters. -/
theorem nodup_positiveInteriorRealRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.positiveInteriorRealRootValues.Nodup := by
  classical
  simpa [positiveInteriorRealRootValues] using
    List.nodup_dedup (((data.roots.toList.filter
      IsPositiveInteriorRealRootRepresentative).map fun z => z.re))

/-- The positive outside-real representative list has no duplicate
parameters. -/
theorem nodup_positiveOutsideRealRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.positiveOutsideRealRootValues.Nodup := by
  classical
  simpa [positiveOutsideRealRootValues] using
    List.nodup_dedup (((data.roots.toList.filter
      IsPositiveOutsideRealRootRepresentative).map fun z => z.re))

/-- The positive-imaginary representative list has no duplicate radii. -/
theorem nodup_positiveImaginaryRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.positiveImaginaryRootValues.Nodup := by
  classical
  simpa [positiveImaginaryRootValues] using
    List.nodup_dedup (((data.roots.toList.filter
      IsPositiveImaginaryRootRepresentative).map fun z => z.im))

/-- The first-quadrant complex representative list has no duplicate
parameters. -/
theorem nodup_firstQuadrantComplexRootValues {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.firstQuadrantComplexRootValues.Nodup := by
  classical
  simpa [firstQuadrantComplexRootValues] using
    List.nodup_dedup (((data.roots.toList.filter
      IsFirstQuadrantComplexRootRepresentative).map fun z => (z.re, z.im)))

/-- The complex first-quadrant representative list has no duplicate roots. -/
theorem nodup_firstQuadrantComplexRootRepresentatives {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.firstQuadrantComplexRootRepresentatives.Nodup := by
  classical
  simpa [firstQuadrantComplexRootRepresentatives] using
    (List.nodup_dedup data.roots.toList).filter
      (p := fun z : ℂ => decide (IsFirstQuadrantComplexRootRepresentative z))

/-- Membership in the positive-interior representative list recovers the
source interval condition. -/
theorem mem_positiveInteriorRealRootValues {A : ℝ[X]} {data : SourceRootProductData A}
    {s : ℝ} (hs : s ∈ data.positiveInteriorRealRootValues) :
    0 < s ∧ s < 1 := by
  classical
  rw [positiveInteriorRealRootValues, List.mem_dedup] at hs
  rcases List.mem_map.mp hs with ⟨z, hz, rfl⟩
  have hpred : IsPositiveInteriorRealRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  exact hpred.2

/-- A positive-interior representative from the root multiset is selected by
the source representative list [GSLW19, BlockHam.tex:450-456]. -/
theorem mem_positiveInteriorRealRootValues_of_root_mem
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.roots) (hrep : IsPositiveInteriorRealRootRepresentative z) :
    z.re ∈ data.positiveInteriorRealRootValues := by
  classical
  rw [positiveInteriorRealRootValues, List.mem_dedup]
  exact List.mem_map.mpr ⟨z, by
    exact List.mem_filter.mpr ⟨Multiset.mem_toList.mpr hz,
      show decide (IsPositiveInteriorRealRootRepresentative z) = true from
        decide_eq_true hrep⟩, rfl⟩

/-- Membership in the positive-outside representative list recovers the
`1 <= s` condition used by the real-root source factor. -/
theorem mem_positiveOutsideRealRootValues {A : ℝ[X]} {data : SourceRootProductData A}
    {s : ℝ} (hs : s ∈ data.positiveOutsideRealRootValues) :
    1 ≤ s := by
  classical
  rw [positiveOutsideRealRootValues, List.mem_dedup] at hs
  rcases List.mem_map.mp hs with ⟨z, hz, rfl⟩
  have hpred : IsPositiveOutsideRealRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  exact hpred.2

/-- A positive outside-real representative from the root multiset is selected
by the source representative list [GSLW19, BlockHam.tex:450-456]. -/
theorem mem_positiveOutsideRealRootValues_of_root_mem
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.roots) (hrep : IsPositiveOutsideRealRootRepresentative z) :
    z.re ∈ data.positiveOutsideRealRootValues := by
  classical
  rw [positiveOutsideRealRootValues, List.mem_dedup]
  exact List.mem_map.mpr ⟨z, by
    exact List.mem_filter.mpr ⟨Multiset.mem_toList.mpr hz,
      show decide (IsPositiveOutsideRealRootRepresentative z) = true from
        decide_eq_true hrep⟩, rfl⟩

/-- Membership in the positive-imaginary representative list recovers the
positive radius condition. -/
theorem mem_positiveImaginaryRootValues {A : ℝ[X]} {data : SourceRootProductData A}
    {r : ℝ} (hr : r ∈ data.positiveImaginaryRootValues) :
    0 < r := by
  classical
  rw [positiveImaginaryRootValues, List.mem_dedup] at hr
  rcases List.mem_map.mp hr with ⟨z, hz, rfl⟩
  have hpred : IsPositiveImaginaryRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  exact hpred.2

/-- A positive imaginary representative from the root multiset is selected by
the source representative list [GSLW19, BlockHam.tex:450-456]. -/
theorem mem_positiveImaginaryRootValues_of_root_mem
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.roots) (hrep : IsPositiveImaginaryRootRepresentative z) :
    z.im ∈ data.positiveImaginaryRootValues := by
  classical
  rw [positiveImaginaryRootValues, List.mem_dedup]
  exact List.mem_map.mpr ⟨z, by
    exact List.mem_filter.mpr ⟨Multiset.mem_toList.mpr hz,
      show decide (IsPositiveImaginaryRootRepresentative z) = true from
        decide_eq_true hrep⟩, rfl⟩

/-- Membership in the first-quadrant representative list recovers the positive
real and imaginary parts used by the complex quartet factor. -/
theorem mem_firstQuadrantComplexRootValues {A : ℝ[X]} {data : SourceRootProductData A}
    {z : ℝ × ℝ} (hz : z ∈ data.firstQuadrantComplexRootValues) :
    0 < z.1 ∧ 0 < z.2 := by
  classical
  rw [firstQuadrantComplexRootValues, List.mem_dedup] at hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  have hpred : IsFirstQuadrantComplexRootRepresentative w :=
    of_decide_eq_true (List.mem_filter.mp hw).2
  exact hpred

/-- A first-quadrant representative from the root multiset is selected by the
source representative list [GSLW19, BlockHam.tex:450-456]. -/
theorem mem_firstQuadrantComplexRootValues_of_root_mem
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.roots) (hrep : IsFirstQuadrantComplexRootRepresentative z) :
    (z.re, z.im) ∈ data.firstQuadrantComplexRootValues := by
  classical
  rw [firstQuadrantComplexRootValues, List.mem_dedup]
  exact List.mem_map.mpr ⟨z, by
    exact List.mem_filter.mpr ⟨Multiset.mem_toList.mpr hz,
      show decide (IsFirstQuadrantComplexRootRepresentative z) = true from
        decide_eq_true hrep⟩, rfl⟩

/-- Membership in the complex first-quadrant representative list recovers the
root predicate and the original root-multiset membership. -/
theorem mem_firstQuadrantComplexRootRepresentatives
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.firstQuadrantComplexRootRepresentatives) :
    IsFirstQuadrantComplexRootRepresentative z ∧ z ∈ data.roots := by
  classical
  rw [firstQuadrantComplexRootRepresentatives] at hz
  have hfilter := List.mem_filter.mp hz
  exact ⟨of_decide_eq_true hfilter.2,
    Multiset.mem_toList.mp (List.mem_dedup.mp hfilter.1)⟩

/-- A positive-interior real representative is a root in the source multiset. -/
theorem root_mem_of_mem_positiveInteriorRealRootValues
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.positiveInteriorRealRootValues) :
    (s : ℂ) ∈ data.roots := by
  classical
  rw [positiveInteriorRealRootValues, List.mem_dedup] at hs
  rcases List.mem_map.mp hs with ⟨z, hz, rfl⟩
  have hmem : z ∈ data.roots.toList := (List.mem_filter.mp hz).1
  have hpred : IsPositiveInteriorRealRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  have hz_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hpred.1
  rw [← hz_eq]
  exact Multiset.mem_toList.mp hmem

/-- A positive outside-real representative is a root in the source multiset. -/
theorem root_mem_of_mem_positiveOutsideRealRootValues
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.positiveOutsideRealRootValues) :
    (s : ℂ) ∈ data.roots := by
  classical
  rw [positiveOutsideRealRootValues, List.mem_dedup] at hs
  rcases List.mem_map.mp hs with ⟨z, hz, rfl⟩
  have hmem : z ∈ data.roots.toList := (List.mem_filter.mp hz).1
  have hpred : IsPositiveOutsideRealRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  have hz_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hpred.1
  rw [← hz_eq]
  exact Multiset.mem_toList.mp hmem

/-- A positive imaginary representative is a root in the source multiset. -/
theorem root_mem_of_mem_positiveImaginaryRootValues
    {A : ℝ[X]} {data : SourceRootProductData A} {r : ℝ}
    (hr : r ∈ data.positiveImaginaryRootValues) :
    Complex.I * (r : ℂ) ∈ data.roots := by
  classical
  rw [positiveImaginaryRootValues, List.mem_dedup] at hr
  rcases List.mem_map.mp hr with ⟨z, hz, rfl⟩
  have hmem : z ∈ data.roots.toList := (List.mem_filter.mp hz).1
  have hpred : IsPositiveImaginaryRootRepresentative z :=
    of_decide_eq_true (List.mem_filter.mp hz).2
  have hz_eq : z = Complex.I * (z.im : ℂ) := by
    apply Complex.ext
    · simpa using hpred.1
    · simp
  rw [← hz_eq]
  exact Multiset.mem_toList.mp hmem

/-- A first-quadrant complex representative is a root in the source multiset. -/
theorem root_mem_of_mem_firstQuadrantComplexRootValues
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℝ × ℝ}
    (hz : z ∈ data.firstQuadrantComplexRootValues) :
    ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ∈ data.roots := by
  classical
  rw [firstQuadrantComplexRootValues, List.mem_dedup] at hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  have hmem : w ∈ data.roots.toList := (List.mem_filter.mp hw).1
  have h_eq : w = (w.re : ℂ) + Complex.I * (w.im : ℂ) := by
    apply Complex.ext <;> simp
  rw [← h_eq]
  exact Multiset.mem_toList.mp hmem

/-- Interior real-root pair parameters repeated according to half the complex
root multiplicity, matching the squared-pair factors in [GSLW19,
BlockHam.tex:445,469-474]. -/
noncomputable def interiorRealRootPairParameters {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ :=
  data.positiveInteriorRealRootValues.flatMap fun s : ℝ =>
    let z : ℂ := s
    List.replicate ((realPolynomialToComplex A).rootMultiplicity z / 2) s

/-- Positive endpoint/outside real-root parameters repeated by their complex
root multiplicity.  These become `OutsideRealRoot` values once the outside
condition is attached later in the file. -/
noncomputable def outsideRealRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ :=
  data.positiveOutsideRealRootValues.flatMap fun s : ℝ =>
    let z : ℂ := s
    List.replicate ((realPolynomialToComplex A).rootMultiplicity z) s

/-- Positive imaginary-root parameters repeated by their complex root
multiplicity [GSLW19, BlockHam.tex:455,461]. -/
noncomputable def imaginaryRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) : List ℝ :=
  data.positiveImaginaryRootValues.flatMap fun r : ℝ =>
    let z : ℂ := Complex.I * (r : ℂ)
    List.replicate ((realPolynomialToComplex A).rootMultiplicity z) r

/-- First-quadrant non-real root parameters repeated by their complex root
multiplicity [GSLW19, BlockHam.tex:455-456,462-466]. -/
noncomputable def complexRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) : List (ℝ × ℝ) :=
  data.firstQuadrantComplexRootRepresentatives.flatMap fun z =>
    List.replicate ((realPolynomialToComplex A).rootMultiplicity
      z) (z.re, z.im)

/-- Length of the multiplicity-expanded interior real-root parameter list. -/
theorem length_interiorRealRootPairParameters {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.interiorRealRootPairParameters.length =
      (data.positiveInteriorRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum := by
  simp [interiorRealRootPairParameters, List.length_flatMap]

/-- Length of the multiplicity-expanded outside real-root parameter list. -/
theorem length_outsideRealRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.outsideRealRootParameters.length =
      (data.positiveOutsideRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum := by
  simp [outsideRealRootParameters, List.length_flatMap]

/-- Length of the multiplicity-expanded imaginary-root parameter list. -/
theorem length_imaginaryRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.imaginaryRootParameters.length =
      (data.positiveImaginaryRootValues.map fun r : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum := by
  simp [imaginaryRootParameters, List.length_flatMap]

/-- Length of the multiplicity-expanded first-quadrant complex-root parameter
list. -/
theorem length_complexRootParameters {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.complexRootParameters.length =
      (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
        (realPolynomialToComplex A).rootMultiplicity z).sum := by
  simp [complexRootParameters, List.length_flatMap]

/-- Summing the canonical multiplicities over selected positive interior
representatives gives the positive-interior root-class count. -/
theorem sum_count_positiveInteriorRealRootValues_eq_countP {A : ℝ[X]}
    (data : SourceRootProductData A) :
    (data.positiveInteriorRealRootValues.map fun s : ℝ =>
        data.roots.count (s : ℂ)).sum =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) data.roots := by
  classical
  rw [positiveInteriorRealRootValues]
  have hmap :
      (((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ => data.roots.count (s : ℂ)).sum =
        (((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ =>
            List.count s ((data.roots.toList.filter
              IsPositiveInteriorRealRootRepresentative).map fun z => z.re)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    have hscond : 0 < s ∧ s < 1 :=
      mem_positiveInteriorRealRootValues (data := data) (by
        simpa [positiveInteriorRealRootValues] using hs)
    rw [list_count_positiveInterior_re_filter data.roots.toList hscond]
    change data.roots.count (s : ℂ) = List.count (s : ℂ) data.roots.toList
    rw [← Multiset.coe_count (s : ℂ) data.roots.toList, Multiset.coe_toList]
  calc
    (((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
        fun z => z.re).dedup.map fun s : ℝ => data.roots.count (s : ℂ)).sum =
        (((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ =>
            List.count s ((data.roots.toList.filter
              IsPositiveInteriorRealRootRepresentative).map fun z => z.re)).sum := hmap
    _ =
        ((data.roots.toList.filter IsPositiveInteriorRealRootRepresentative).map
          fun z => z.re).length := by
      exact List.sum_map_count_dedup_eq_length _
    _ =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) data.roots := by
      rw [List.length_map, ← List.countP_eq_length_filter]
      rw [← Multiset.coe_countP
        (p := IsPositiveInteriorRealRootRepresentative) data.roots.toList,
        Multiset.coe_toList]

/-- Summing the canonical multiplicities over selected outside-real
representatives gives the outside-real root-class count. -/
theorem sum_count_positiveOutsideRealRootValues_eq_countP {A : ℝ[X]}
    (data : SourceRootProductData A) :
    (data.positiveOutsideRealRootValues.map fun s : ℝ =>
        data.roots.count (s : ℂ)).sum =
      @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) data.roots := by
  classical
  rw [positiveOutsideRealRootValues]
  have hmap :
      (((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ => data.roots.count (s : ℂ)).sum =
        (((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ =>
            List.count s ((data.roots.toList.filter
              IsPositiveOutsideRealRootRepresentative).map fun z => z.re)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s hs
    have hscond : 1 ≤ s :=
      mem_positiveOutsideRealRootValues (data := data) (by
        simpa [positiveOutsideRealRootValues] using hs)
    rw [list_count_positiveOutside_re_filter data.roots.toList hscond]
    change data.roots.count (s : ℂ) = List.count (s : ℂ) data.roots.toList
    rw [← Multiset.coe_count (s : ℂ) data.roots.toList, Multiset.coe_toList]
  calc
    (((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
        fun z => z.re).dedup.map fun s : ℝ => data.roots.count (s : ℂ)).sum =
        (((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
          fun z => z.re).dedup.map fun s : ℝ =>
            List.count s ((data.roots.toList.filter
              IsPositiveOutsideRealRootRepresentative).map fun z => z.re)).sum := hmap
    _ =
        ((data.roots.toList.filter IsPositiveOutsideRealRootRepresentative).map
          fun z => z.re).length := by
      exact List.sum_map_count_dedup_eq_length _
    _ =
      @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) data.roots := by
      rw [List.length_map, ← List.countP_eq_length_filter]
      rw [← Multiset.coe_countP
        (p := IsPositiveOutsideRealRootRepresentative) data.roots.toList,
        Multiset.coe_toList]

/-- Summing the canonical multiplicities over selected positive-imaginary
representatives gives the positive-imaginary root-class count. -/
theorem sum_count_positiveImaginaryRootValues_eq_countP {A : ℝ[X]}
    (data : SourceRootProductData A) :
    (data.positiveImaginaryRootValues.map fun r : ℝ =>
        data.roots.count (Complex.I * (r : ℂ))).sum =
      @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) data.roots := by
  classical
  rw [positiveImaginaryRootValues]
  have hmap :
      (((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
          fun z => z.im).dedup.map fun r : ℝ =>
            data.roots.count (Complex.I * (r : ℂ))).sum =
        (((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
          fun z => z.im).dedup.map fun r : ℝ =>
            List.count r ((data.roots.toList.filter
              IsPositiveImaginaryRootRepresentative).map fun z => z.im)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    have hrcond : 0 < r :=
      mem_positiveImaginaryRootValues (data := data) (by
        simpa [positiveImaginaryRootValues] using hr)
    rw [list_count_positiveImaginary_im_filter data.roots.toList hrcond]
    change data.roots.count (Complex.I * (r : ℂ)) =
      List.count (Complex.I * (r : ℂ)) data.roots.toList
    rw [← Multiset.coe_count (Complex.I * (r : ℂ)) data.roots.toList,
      Multiset.coe_toList]
  calc
    (((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
        fun z => z.im).dedup.map fun r : ℝ =>
          data.roots.count (Complex.I * (r : ℂ))).sum =
        (((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
          fun z => z.im).dedup.map fun r : ℝ =>
            List.count r ((data.roots.toList.filter
              IsPositiveImaginaryRootRepresentative).map fun z => z.im)).sum := hmap
    _ =
        ((data.roots.toList.filter IsPositiveImaginaryRootRepresentative).map
          fun z => z.im).length := by
      exact List.sum_map_count_dedup_eq_length _
    _ =
      @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) data.roots := by
      rw [List.length_map, ← List.countP_eq_length_filter]
      rw [← Multiset.coe_countP
        (p := IsPositiveImaginaryRootRepresentative) data.roots.toList,
        Multiset.coe_toList]

/-- Summing canonical multiplicities over the complex first-quadrant
representatives gives the first-quadrant root-class count. -/
theorem sum_count_firstQuadrantComplexRootRepresentatives_eq_countP {A : ℝ[X]}
    (data : SourceRootProductData A) :
    (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
        data.roots.count z).sum =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
  classical
  rw [firstQuadrantComplexRootRepresentatives]
  have hmap :
      ((data.roots.toList.dedup.filter IsFirstQuadrantComplexRootRepresentative).map
          fun z : ℂ => data.roots.count z).sum =
        ((data.roots.toList.dedup.filter IsFirstQuadrantComplexRootRepresentative).map
          fun z : ℂ => List.count z data.roots.toList).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro z _hz
    rw [← Multiset.coe_count z data.roots.toList, Multiset.coe_toList]
  calc
    ((data.roots.toList.dedup.filter IsFirstQuadrantComplexRootRepresentative).map
        fun z : ℂ => data.roots.count z).sum =
        ((data.roots.toList.dedup.filter IsFirstQuadrantComplexRootRepresentative).map
          fun z : ℂ => List.count z data.roots.toList).sum := hmap
    _ =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
      calc
        (List.map (fun z : ℂ => List.count z data.roots.toList)
            (List.filter (fun z : ℂ =>
              decide (IsFirstQuadrantComplexRootRepresentative z))
                data.roots.toList.dedup)).sum =
            List.countP
              (fun z : ℂ => decide (IsFirstQuadrantComplexRootRepresentative z))
              data.roots.toList := by
          exact List.sum_map_count_dedup_filter_eq_countP
            (p := fun z : ℂ =>
              decide (IsFirstQuadrantComplexRootRepresentative z))
            data.roots.toList
        _ =
          @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
            (fun z => Classical.propDecidable
              (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
          rw [← Multiset.coe_countP
            (p := IsFirstQuadrantComplexRootRepresentative) data.roots.toList,
            Multiset.coe_toList]

/-- Parameters repeated for interior real-root factors still satisfy the
interior condition and come from the source root multiset. -/
theorem mem_interiorRealRootPairParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.interiorRealRootPairParameters) :
    (0 < s ∧ s < 1) ∧ (s : ℂ) ∈ data.roots := by
  classical
  rw [interiorRealRootPairParameters] at hs
  rcases List.mem_flatMap.mp hs with ⟨t, ht, hrep⟩
  have hst : s = t := (List.mem_replicate.mp hrep).2
  subst hst
  exact ⟨mem_positiveInteriorRealRootValues (data := data) ht,
    root_mem_of_mem_positiveInteriorRealRootValues (data := data) ht⟩

/-- Parameters repeated for outside real-root factors still satisfy the outside
condition and come from the source root multiset. -/
theorem mem_outsideRealRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.outsideRealRootParameters) :
    1 ≤ s ∧ (s : ℂ) ∈ data.roots := by
  classical
  rw [outsideRealRootParameters] at hs
  rcases List.mem_flatMap.mp hs with ⟨t, ht, hrep⟩
  have hst : s = t := (List.mem_replicate.mp hrep).2
  subst hst
  exact ⟨mem_positiveOutsideRealRootValues (data := data) ht,
    root_mem_of_mem_positiveOutsideRealRootValues (data := data) ht⟩

/-- Parameters repeated for imaginary-root factors still have positive radius
and come from the source root multiset. -/
theorem mem_imaginaryRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {r : ℝ}
    (hr : r ∈ data.imaginaryRootParameters) :
    0 < r ∧ Complex.I * (r : ℂ) ∈ data.roots := by
  classical
  rw [imaginaryRootParameters] at hr
  rcases List.mem_flatMap.mp hr with ⟨t, ht, hrep⟩
  have hrt : r = t := (List.mem_replicate.mp hrep).2
  subst hrt
  exact ⟨mem_positiveImaginaryRootValues (data := data) ht,
    root_mem_of_mem_positiveImaginaryRootValues (data := data) ht⟩

/-- Parameters repeated for complex quartet factors still have positive real
and imaginary parts and come from the source root multiset. -/
theorem mem_complexRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℝ × ℝ}
    (hz : z ∈ data.complexRootParameters) :
    (0 < z.1 ∧ 0 < z.2) ∧
      ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ∈ data.roots := by
  classical
  rw [complexRootParameters] at hz
  rcases List.mem_flatMap.mp hz with ⟨(w : ℂ), hw, hrep⟩
  have hzw : z = (w.re, w.im) := (List.mem_replicate.mp hrep).2
  subst hzw
  have hw' := mem_firstQuadrantComplexRootRepresentatives (data := data) hw
  have hw_cart : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
    apply Complex.ext <;> simp
  exact ⟨hw'.1, by simpa [hw_cart] using hw'.2⟩

/-- The multiplicity-expanded interior parameter list contains each selected
positive representative exactly half of its canonical multiplicity
[GSLW19, BlockHam.tex:445,452-454,469-479]. -/
theorem count_interiorRealRootPairParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.positiveInteriorRealRootValues) :
    data.interiorRealRootPairParameters.count s =
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2 := by
  classical
  rw [interiorRealRootPairParameters,
    list_count_flatMap_replicate_self]
  · simp [hs]
  · exact data.nodup_positiveInteriorRealRootValues

/-- The multiplicity-expanded outside-real parameter list contains each
selected positive outside root exactly its canonical multiplicity
[GSLW19, BlockHam.tex:446,453-460,469-479]. -/
theorem count_outsideRealRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {s : ℝ}
    (hs : s ∈ data.positiveOutsideRealRootValues) :
    data.outsideRealRootParameters.count s =
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) := by
  classical
  rw [outsideRealRootParameters,
    list_count_flatMap_replicate_self]
  · simp [hs]
  · exact data.nodup_positiveOutsideRealRootValues

/-- The multiplicity-expanded imaginary parameter list contains each selected
positive imaginary radius exactly its canonical multiplicity
[GSLW19, BlockHam.tex:447,455,461,469-479]. -/
theorem count_imaginaryRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {r : ℝ}
    (hr : r ∈ data.positiveImaginaryRootValues) :
    data.imaginaryRootParameters.count r =
      (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ)) := by
  classical
  rw [imaginaryRootParameters,
    list_count_flatMap_replicate_self]
  · simp [hr]
  · exact data.nodup_positiveImaginaryRootValues

/-- The multiplicity-expanded complex-quartet parameter list contains each
selected first-quadrant representative exactly its canonical multiplicity
[GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem count_complexRootParameters
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℂ}
    (hz : z ∈ data.firstQuadrantComplexRootRepresentatives) :
    data.complexRootParameters.count (z.re, z.im) =
      (realPolynomialToComplex A).rootMultiplicity z := by
  classical
  rw [complexRootParameters]
  have hkey_nodup :
      (data.firstQuadrantComplexRootRepresentatives.map
        (fun z : ℂ => (z.re, z.im))).Nodup := by
    have hinj : Function.Injective (fun z : ℂ => (z.re, z.im)) := by
      intro z w h
      apply Complex.ext
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h
    exact data.nodup_firstQuadrantComplexRootRepresentatives.map hinj
  exact list_count_flatMap_replicate_key_of_mem
    data.firstQuadrantComplexRootRepresentatives
    (fun z : ℂ => (z.re, z.im))
    (fun z : ℂ => (realPolynomialToComplex A).rootMultiplicity z)
    hkey_nodup hz

theorem count_complexRootParameters_of_mem
    {A : ℝ[X]} {data : SourceRootProductData A} {z : ℝ × ℝ}
    (hz : z ∈ data.complexRootParameters) :
    data.complexRootParameters.count z =
      (realPolynomialToComplex A).rootMultiplicity
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := by
  classical
  rw [complexRootParameters] at hz ⊢
  rcases List.mem_flatMap.mp hz with ⟨w, hw, hzrep⟩
  have hz_eq : z = (w.re, w.im) := List.eq_of_mem_replicate hzrep
  subst z
  have hw_eq : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
    apply Complex.ext <;> simp
  rw [hw_eq]
  exact count_complexRootParameters (data := data) hw

end SourceRootProductData

/-- Every canonical source root has an orbit representative selected by one
of the source representative lists, except for the zero class which is tracked
by `zeroRootPairs` [GSLW19, BlockHam.tex:450-456]. -/
theorem SourceHypotheses.exists_selected_sourceRepresentative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    {z : ℂ} (hz : z ∈ (hA.rootProductData).roots) :
    ∃ w, w ∈ (hA.rootProductData).roots ∧ w ∈ complexRootOrbit z ∧
      (w = 0 ∨
        w.re ∈ (hA.rootProductData).positiveInteriorRealRootValues ∨
        w.re ∈ (hA.rootProductData).positiveOutsideRealRootValues ∨
        w.im ∈ (hA.rootProductData).positiveImaginaryRootValues ∨
        (w.re, w.im) ∈ (hA.rootProductData).firstQuadrantComplexRootValues) := by
  rcases hA.exists_sourceRepresentative_mem_rootProductData hz with
    ⟨w, hw_mem, hw_orbit, hw_rep⟩
  refine ⟨w, hw_mem, hw_orbit, ?_⟩
  rcases hw_rep with hzero | hinterior | houtside | himag | hcomplex
  · exact Or.inl hzero
  · exact Or.inr (Or.inl
      (SourceRootProductData.mem_positiveInteriorRealRootValues_of_root_mem
        (data := hA.rootProductData) hw_mem hinterior))
  · exact Or.inr (Or.inr (Or.inl
      (SourceRootProductData.mem_positiveOutsideRealRootValues_of_root_mem
        (data := hA.rootProductData) hw_mem houtside)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (SourceRootProductData.mem_positiveImaginaryRootValues_of_root_mem
        (data := hA.rootProductData) hw_mem himag))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (SourceRootProductData.mem_firstQuadrantComplexRootValues_of_root_mem
        (data := hA.rootProductData) hw_mem hcomplex))))

/-- A selected positive-interior representative contributes to the
positive-interior root-class filter. -/
theorem SourceHypotheses.count_le_countP_positiveInterior_of_mem
    {A : ℝ[X]} {k : ℕ} [DecidablePred IsPositiveInteriorRealRootRepresentative]
    (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ (hA.rootProductData).positiveInteriorRealRootValues) :
    (hA.rootProductData).roots.count (s : ℂ) ≤
      (hA.rootProductData).roots.countP IsPositiveInteriorRealRootRepresentative := by
  classical
  have hscond := SourceRootProductData.mem_positiveInteriorRealRootValues
    (data := hA.rootProductData) hs
  exact multiset_count_le_countP_of (hA.rootProductData).roots
    (a := (s : ℂ)) (p := IsPositiveInteriorRealRootRepresentative) (by
      exact ⟨by simp, hscond⟩)

/-- A selected positive outside-real representative contributes to the
outside-real root-class filter. -/
theorem SourceHypotheses.count_le_countP_positiveOutside_of_mem
    {A : ℝ[X]} {k : ℕ} [DecidablePred IsPositiveOutsideRealRootRepresentative]
    (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ (hA.rootProductData).positiveOutsideRealRootValues) :
    (hA.rootProductData).roots.count (s : ℂ) ≤
      (hA.rootProductData).roots.countP IsPositiveOutsideRealRootRepresentative := by
  classical
  have hscond := SourceRootProductData.mem_positiveOutsideRealRootValues
    (data := hA.rootProductData) hs
  exact multiset_count_le_countP_of (hA.rootProductData).roots
    (a := (s : ℂ)) (p := IsPositiveOutsideRealRootRepresentative) (by
      exact ⟨by simp, hscond⟩)

/-- A selected positive-imaginary representative contributes to the
positive-imaginary root-class filter. -/
theorem SourceHypotheses.count_le_countP_positiveImaginary_of_mem
    {A : ℝ[X]} {k : ℕ} [DecidablePred IsPositiveImaginaryRootRepresentative]
    (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ (hA.rootProductData).positiveImaginaryRootValues) :
    (hA.rootProductData).roots.count (Complex.I * (r : ℂ)) ≤
      (hA.rootProductData).roots.countP IsPositiveImaginaryRootRepresentative := by
  classical
  have hrcond := SourceRootProductData.mem_positiveImaginaryRootValues
    (data := hA.rootProductData) hr
  exact multiset_count_le_countP_of (hA.rootProductData).roots
    (a := Complex.I * (r : ℂ)) (p := IsPositiveImaginaryRootRepresentative) (by
      constructor
      · simp
      · simpa using hrcond)

/-- A selected first-quadrant representative contributes to the complex
first-quadrant root-class filter. -/
theorem SourceHypotheses.count_le_countP_firstQuadrant_of_mem
    {A : ℝ[X]} {k : ℕ} [DecidablePred IsFirstQuadrantComplexRootRepresentative]
    (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ (hA.rootProductData).firstQuadrantComplexRootValues) :
    (hA.rootProductData).roots.count ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) ≤
      (hA.rootProductData).roots.countP IsFirstQuadrantComplexRootRepresentative := by
  classical
  have hzcond := SourceRootProductData.mem_firstQuadrantComplexRootValues
    (data := hA.rootProductData) hz
  exact multiset_count_le_countP_of (hA.rootProductData).roots
    (a := ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))
    (p := IsFirstQuadrantComplexRootRepresentative) (by
      simpa [IsFirstQuadrantComplexRootRepresentative] using hzcond)

/-- If an interior positive real representative is selected from canonical
source roots, then its negative partner is also a source root.  This packages
one of the paired roots used in [GSLW19, BlockHam.tex:445,452-454]. -/
theorem SourceHypotheses.neg_mem_rootProductData_of_mem_positiveInterior
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ (hA.rootProductData).positiveInteriorRealRootValues) :
    -(s : ℂ) ∈ (hA.rootProductData).roots := by
  exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit
    (SourceRootProductData.root_mem_of_mem_positiveInteriorRealRootValues
      (data := hA.rootProductData) hs)
    (by simp [complexRootOrbit])

/-- Positive interior representatives and their negative partners have equal
canonical-root counts [GSLW19, BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.count_neg_eq_of_mem_positiveInterior
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (_hs : s ∈ (hA.rootProductData).positiveInteriorRealRootValues) :
    (hA.rootProductData).roots.count (-(s : ℂ)) =
      (hA.rootProductData).roots.count (s : ℂ) := by
  exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
    (z := (s : ℂ)) (w := -(s : ℂ)) (by simp [complexRootOrbit])

/-- Positive outside-real representatives and their negative partners have
equal canonical-root counts [GSLW19, BlockHam.tex:453-460,469-479]. -/
theorem SourceHypotheses.count_neg_eq_of_mem_positiveOutside
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (_hs : s ∈ (hA.rootProductData).positiveOutsideRealRootValues) :
    (hA.rootProductData).roots.count (-(s : ℂ)) =
      (hA.rootProductData).roots.count (s : ℂ) := by
  exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
    (z := (s : ℂ)) (w := -(s : ℂ)) (by simp [complexRootOrbit])

/-- If a positive imaginary representative is selected from canonical source
roots, then the negative imaginary partner is also a source root
[GSLW19, BlockHam.tex:455,461]. -/
theorem SourceHypotheses.neg_imag_mem_rootProductData_of_mem_positiveImaginary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ (hA.rootProductData).positiveImaginaryRootValues) :
    -(Complex.I * (r : ℂ)) ∈ (hA.rootProductData).roots := by
  exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit
    (SourceRootProductData.root_mem_of_mem_positiveImaginaryRootValues
      (data := hA.rootProductData) hr)
    (by simp [complexRootOrbit])

/-- Positive imaginary representatives and their negative partners have equal
canonical-root counts [GSLW19, BlockHam.tex:455,461,469-479]. -/
theorem SourceHypotheses.count_neg_imag_eq_of_mem_positiveImaginary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (_hr : r ∈ (hA.rootProductData).positiveImaginaryRootValues) :
    (hA.rootProductData).roots.count (-(Complex.I * (r : ℂ))) =
      (hA.rootProductData).roots.count (Complex.I * (r : ℂ)) := by
  exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
    (z := Complex.I * (r : ℂ)) (w := -(Complex.I * (r : ℂ)))
    (by simp [complexRootOrbit])

/-- A first-quadrant representative selected from canonical source roots brings
all three companion roots in the quartet [GSLW19, BlockHam.tex:455-456,
462-466]. -/
theorem SourceHypotheses.complex_quartet_mem_rootProductData_of_mem_firstQuadrant
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ (hA.rootProductData).firstQuadrantComplexRootValues) :
    let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ);
    -w ∈ (hA.rootProductData).roots ∧
      starRingEnd ℂ w ∈ (hA.rootProductData).roots ∧
        -(starRingEnd ℂ w) ∈ (hA.rootProductData).roots := by
  intro w
  have hw : w ∈ (hA.rootProductData).roots :=
    SourceRootProductData.root_mem_of_mem_firstQuadrantComplexRootValues
      (data := hA.rootProductData) hz
  constructor
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])
  constructor
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])

/-- The four members of a selected complex quartet have equal canonical-root
counts [GSLW19, BlockHam.tex:455-456,462-466,469-479]. -/
theorem SourceHypotheses.complex_quartet_count_eq_of_mem_firstQuadrant
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (_hz : z ∈ (hA.rootProductData).firstQuadrantComplexRootValues) :
    let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
    (hA.rootProductData).roots.count (-w) =
        (hA.rootProductData).roots.count w ∧
      (hA.rootProductData).roots.count (starRingEnd ℂ w) =
        (hA.rootProductData).roots.count w ∧
      (hA.rootProductData).roots.count (-(starRingEnd ℂ w)) =
        (hA.rootProductData).roots.count w := by
  intro w
  constructor
  · exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
      (z := w) (w := -w) (by simp [complexRootOrbit])
  constructor
  · exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
      (z := w) (w := starRingEnd ℂ w) (by simp [complexRootOrbit])
  · exact hA.rootProductData_count_eq_of_mem_complexRootOrbit
      (z := w) (w := -(starRingEnd ℂ w)) (by simp [complexRootOrbit])

/-- Expanded interior real-root parameters still bring their negative partners
in the canonical root multiset [GSLW19, BlockHam.tex:445,452-454]. -/
theorem SourceHypotheses.neg_mem_rootProductData_of_mem_interiorRealRootPairParameters
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ (hA.rootProductData).interiorRealRootPairParameters) :
    -(s : ℂ) ∈ (hA.rootProductData).roots := by
  have hsroot : (s : ℂ) ∈ (hA.rootProductData).roots :=
    (SourceRootProductData.mem_interiorRealRootPairParameters
      (data := hA.rootProductData) hs).2
  exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hsroot
    (by simp [complexRootOrbit])

/-- Expanded imaginary-root parameters still bring their negative imaginary
partners in the canonical root multiset [GSLW19, BlockHam.tex:455,461]. -/
theorem SourceHypotheses.neg_imag_mem_rootProductData_of_mem_imaginaryRootParameters
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ (hA.rootProductData).imaginaryRootParameters) :
    -(Complex.I * (r : ℂ)) ∈ (hA.rootProductData).roots := by
  have hrroot : Complex.I * (r : ℂ) ∈ (hA.rootProductData).roots :=
    (SourceRootProductData.mem_imaginaryRootParameters
      (data := hA.rootProductData) hr).2
  exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hrroot
    (by simp [complexRootOrbit])

/-- Expanded complex-root parameters still bring all quartet companions in the
canonical root multiset [GSLW19, BlockHam.tex:455-456,462-466]. -/
theorem SourceHypotheses.complex_quartet_mem_rootProductData_of_mem_complexRootParameters
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ (hA.rootProductData).complexRootParameters) :
    let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ);
    -w ∈ (hA.rootProductData).roots ∧
      starRingEnd ℂ w ∈ (hA.rootProductData).roots ∧
        -(starRingEnd ℂ w) ∈ (hA.rootProductData).roots := by
  intro w
  have hw : w ∈ (hA.rootProductData).roots :=
    (SourceRootProductData.mem_complexRootParameters
      (data := hA.rootProductData) hz).2
  constructor
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])
  constructor
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])
  · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hw
      (by simp [complexRootOrbit])

/-- Real-polynomial parity only depends on the parity index modulo `2`. -/
theorem HasRealParity.congr {P : ℝ[X]} {p q : ℕ} (hP : HasRealParity P p)
    (hpq : p % 2 = q % 2) : HasRealParity P q := by
  intro k hk
  rw [hP k hk, hpq]

theorem two_mul_half_of_even {n : ℕ} (h : Even n) : 2 * (n / 2) = n := by
  rcases h with ⟨m, rfl⟩
  have hdouble : m + m = 2 * m := by omega
  rw [hdouble, Nat.mul_div_right m (by norm_num : 0 < 2)]

private theorem two_mul_sum_map_half_eq_sum_of_even (l : List ℕ)
    (h : ∀ n ∈ l, Even n) :
    2 * (l.map fun n => n / 2).sum = l.sum := by
  induction l with
  | nil =>
      simp
  | cons n ns ih =>
      have hn : Even n := h n (by simp)
      have hns : ∀ m ∈ ns, Even m := by
        intro m hm
        exact h m (by simp [hm])
      simp only [List.map_cons, List.sum_cons]
      rw [Nat.mul_add, ih hns, two_mul_half_of_even hn]

/-- Expanded interior real-root pair parameters multiply to the corresponding
two-point linear-factor products with full root multiplicity
[GSLW19, BlockHam.tex:445,452-454,469-474]. -/
theorem SourceRootProductData.interiorRealRootPair_linearFactorProduct
    {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.interiorRealRootPairParameters.map fun s : ℝ =>
        (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
          ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod =
      (data.positiveInteriorRealRootValues.map fun s : ℝ =>
        (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
          ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
            (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod := by
  classical
  unfold SourceRootProductData.interiorRealRootPairParameters
  simp only [List.map_flatMap, List.map_replicate]
  rw [list_prod_flatMap_replicate]
  apply congrArg List.prod
  apply List.map_congr_left
  intro s hs
  let pair : ℂ[X] :=
    ((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
      ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))
  have hs_interval : s ∈ Set.Ioo (-1 : ℝ) 1 := by
    have hscond := SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := data) hs
    exact ⟨by linarith [hscond.1], hscond.2⟩
  have heven :
      Even ((realPolynomialToComplex A).rootMultiplicity (s : ℂ)) :=
    data.facts.complex_ofReal_interior_multiplicity_even hs_interval
  have htwo :
      2 * ((realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2) =
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ) :=
    two_mul_half_of_even heven
  change
      (pair ^ 2) ^ ((realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2) =
        pair ^ (realPolynomialToComplex A).rootMultiplicity (s : ℂ)
  rw [← pow_mul, htwo]

/-- Expanded pure-imaginary parameters multiply to the corresponding two-point
linear-factor products with full root multiplicity [GSLW19,
BlockHam.tex:447,455,461]. -/
theorem SourceRootProductData.imaginaryRoot_linearFactorProduct
    {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.imaginaryRootParameters.map fun r : ℝ =>
        ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
          ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod =
      (data.positiveImaginaryRootValues.map fun r : ℝ =>
        (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
          ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
            (realPolynomialToComplex A).rootMultiplicity
              (Complex.I * (r : ℂ))).prod := by
  classical
  unfold SourceRootProductData.imaginaryRootParameters
  simp only [List.map_flatMap, List.map_replicate]
  exact list_prod_flatMap_replicate
    data.positiveImaginaryRootValues
    (fun r : ℝ =>
      (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ)))
    (fun r : ℝ =>
      ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
        ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ)))))

/-- Expanded non-real quartet parameters multiply to the corresponding quartet
linear-factor products with full root multiplicity [GSLW19,
BlockHam.tex:448,455-456,462-466]. -/
theorem SourceRootProductData.complexRoot_linearFactorProduct
    {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.complexRootParameters.map fun z : ℝ × ℝ =>
        ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
          (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod =
      (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
        (((complexRootOrbit z).map
          (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
            (realPolynomialToComplex A).rootMultiplicity z).prod := by
  classical
  unfold SourceRootProductData.complexRootParameters
  simp only [List.map_flatMap, List.map_replicate]
  rw [list_prod_flatMap_replicate]
  apply congrArg List.prod
  apply List.map_congr_left
  intro z _hz
  have hz_cart : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z := by
    apply Complex.ext <;> simp
  simp [hz_cart]

namespace SourceRootClassFacts

/-- Multiplicity of a real root after complexifying the source polynomial.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def complexRealRootMultiplicity {A : ℝ[X]} (_facts : SourceRootClassFacts A)
    (s : ℝ) : ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (s : ℂ)

/-- Even-polynomial symmetry identifies the multiplicities of `s` and `-s`
after complexification. -/
theorem complexRealRootMultiplicity_neg {A : ℝ[X]} (facts : SourceRootClassFacts A)
    (s : ℝ) :
    facts.complexRealRootMultiplicity (-s) = facts.complexRealRootMultiplicity s := by
  unfold complexRealRootMultiplicity
  have hneg : ((-s : ℝ) : ℂ) = -(s : ℂ) := by norm_num
  rw [hneg, facts.complex_neg_multiplicity]

/-- Number of paired zero-root factors in the complexified source product.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def zeroRootPairCount {A : ℝ[X]} (_facts : SourceRootClassFacts A) : ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) / 2

/-- The paired zero-root count accounts for all zero-root multiplicity. -/
theorem two_mul_zeroRootPairCount {A : ℝ[X]} (facts : SourceRootClassFacts A) :
    2 * facts.zeroRootPairCount =
      (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) :=
  two_mul_half_of_even facts.complex_zero_multiplicity_even

/-- Number of paired real-root factors for a real root inside `(-1,1)`.
The receiver is retained so later source-root facts can use dot notation. -/
@[nolint unusedArguments]
noncomputable def interiorRealRootPairCount {A : ℝ[X]} (_facts : SourceRootClassFacts A) (s : ℝ) :
    ℕ :=
  (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2

/-- Interior real-root pair counts are invariant under `s ↦ -s`. -/
theorem interiorRealRootPairCount_neg {A : ℝ[X]} (facts : SourceRootClassFacts A)
    (s : ℝ) :
    facts.interiorRealRootPairCount (-s) = facts.interiorRealRootPairCount s := by
  unfold interiorRealRootPairCount
  change facts.complexRealRootMultiplicity (-s) / 2 =
    facts.complexRealRootMultiplicity s / 2
  rw [facts.complexRealRootMultiplicity_neg s]

/-- The paired interior-root count accounts for all multiplicity of a real
root inside `(-1,1)`. -/
theorem two_mul_interiorRealRootPairCount {A : ℝ[X]} (facts : SourceRootClassFacts A)
    {s : ℝ} (hs : s ∈ Set.Ioo (-1 : ℝ) 1) :
    2 * facts.interiorRealRootPairCount s =
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) :=
  two_mul_half_of_even (facts.complex_ofReal_interior_multiplicity_even hs)

end SourceRootClassFacts

/-- Positive-interior representative multiplicities sum to the corresponding
root-class count in the canonical source multiset. -/
theorem SourceHypotheses.sum_rootMultiplicity_positiveInterior_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  have hmap :
      ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum =
        ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (hA.rootProductData).roots.count (s : ℂ)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _hs
    exact (hA.rootProductData_count_eq_rootMultiplicity (s : ℂ)).symm
  rw [hmap, SourceRootProductData.sum_count_positiveInteriorRealRootValues_eq_countP]

/-- Outside-real representative multiplicities sum to the corresponding
root-class count in the canonical source multiset. -/
theorem SourceHypotheses.sum_rootMultiplicity_positiveOutside_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((hA.rootProductData).positiveOutsideRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum =
      @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  have hmap :
      ((hA.rootProductData).positiveOutsideRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum =
        ((hA.rootProductData).positiveOutsideRealRootValues.map fun s : ℝ =>
          (hA.rootProductData).roots.count (s : ℂ)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _hs
    exact (hA.rootProductData_count_eq_rootMultiplicity (s : ℂ)).symm
  rw [hmap, SourceRootProductData.sum_count_positiveOutsideRealRootValues_eq_countP]

/-- Positive-imaginary representative multiplicities sum to the corresponding
root-class count in the canonical source multiset. -/
theorem SourceHypotheses.sum_rootMultiplicity_positiveImaginary_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((hA.rootProductData).positiveImaginaryRootValues.map fun r : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum =
      @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  have hmap :
      ((hA.rootProductData).positiveImaginaryRootValues.map fun r : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum =
        ((hA.rootProductData).positiveImaginaryRootValues.map fun r : ℝ =>
          (hA.rootProductData).roots.count (Complex.I * (r : ℂ))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _hr
    exact (hA.rootProductData_count_eq_rootMultiplicity (Complex.I * (r : ℂ))).symm
  rw [hmap, SourceRootProductData.sum_count_positiveImaginaryRootValues_eq_countP]

/-- First-quadrant representative multiplicities sum to the corresponding
root-class count in the canonical source multiset. -/
theorem SourceHypotheses.sum_rootMultiplicity_firstQuadrant_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((hA.rootProductData).firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
        (realPolynomialToComplex A).rootMultiplicity z).sum =
      @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
        (fun z => Classical.propDecidable
          (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  have hmap :
      ((hA.rootProductData).firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (realPolynomialToComplex A).rootMultiplicity z).sum =
        ((hA.rootProductData).firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (hA.rootProductData).roots.count z).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro z _hz
    exact (hA.rootProductData_count_eq_rootMultiplicity z).symm
  rw [hmap, SourceRootProductData.sum_count_firstQuadrantComplexRootRepresentatives_eq_countP]

/-- Interior real-root pair expansion uses exactly the positive-interior
root-class multiplicity, because those multiplicities are even. -/
theorem SourceHypotheses.two_mul_sum_half_positiveInterior_eq_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    2 * ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  have heven :
      ∀ n ∈ ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)), Even n := by
    intro n hn
    rcases List.mem_map.mp hn with ⟨s, hs, rfl⟩
    have hscond := SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := hA.rootProductData) hs
    exact hA.rootProductData.facts.complex_ofReal_interior_multiplicity_even
      ⟨by linarith [hscond.1], hscond.2⟩
  calc
    2 * ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
        (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum =
        ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum := by
      change 2 * (((hA.rootProductData).positiveInteriorRealRootValues.map
        (((fun n : ℕ => n / 2) ∘ fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)))).sum) =
        ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum
      have h := two_mul_sum_map_half_eq_sum_of_even
        ((hA.rootProductData).positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)) heven
      rw [List.map_map] at h
      exact h
    _ =
      @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
        (fun z => Classical.propDecidable
          (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots :=
      hA.sum_rootMultiplicity_positiveInterior_eq_countP

theorem hasRealParity_zero (p : ℕ) : HasRealParity 0 p := by
  intro k hk
  simp at hk

theorem hasRealParity_C (c : ℝ) {p : ℕ} (hp : p % 2 = 0) :
    HasRealParity (Polynomial.C c) p := by
  intro k hk
  rw [Polynomial.coeff_C] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [hp]
  · simp [Nat.pos_iff_ne_zero.mp hpos] at hk

theorem hasRealParity_one {p : ℕ} (hp : p % 2 = 0) :
    HasRealParity (1 : ℝ[X]) p := by
  simpa using hasRealParity_C (1 : ℝ) hp

theorem HasRealParity.add {P Q : ℝ[X]} {p : ℕ} (hP : HasRealParity P p)
    (hQ : HasRealParity Q p) : HasRealParity (P + Q) p := by
  intro k hk
  rw [Polynomial.coeff_add] at hk
  by_cases h : P.coeff k = 0
  · exact hQ k (by simpa [h] using hk)
  · exact hP k h

theorem HasRealParity.neg {P : ℝ[X]} {p : ℕ} (hP : HasRealParity P p) :
    HasRealParity (-P) p := by
  intro k hk
  rw [Polynomial.coeff_neg, neg_ne_zero] at hk
  exact hP k hk

theorem HasRealParity.sub {P Q : ℝ[X]} {p : ℕ} (hP : HasRealParity P p)
    (hQ : HasRealParity Q p) : HasRealParity (P - Q) p := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

theorem HasRealParity.mul {P Q : ℝ[X]} {p q : ℕ} (hP : HasRealParity P p)
    (hQ : HasRealParity Q q) : HasRealParity (P * Q) (p + q) := by
  intro k hk
  rw [Polynomial.coeff_mul] at hk
  by_contra hpar
  have hterms :
      ∀ c ∈ Finset.antidiagonal k, P.coeff c.1 * Q.coeff c.2 = 0 := by
    intro c hc
    by_cases hPc : P.coeff c.1 = 0
    · simp [hPc]
    by_cases hQc : Q.coeff c.2 = 0
    · simp [hQc]
    have hp := hP c.1 hPc
    have hq := hQ c.2 hQc
    have hsum : c.1 + c.2 = k := Finset.mem_antidiagonal.mp hc
    have hkpar : k % 2 = (p + q) % 2 := by
      omega
    exact (hpar hkpar).elim
  exact hk (Finset.sum_eq_zero hterms)

/-- Multiplying by a real constant does not change parity. -/
theorem HasRealParity.C_mul {P : ℝ[X]} {p : ℕ} (c : ℝ)
    (hP : HasRealParity P p) : HasRealParity (Polynomial.C c * P) p := by
  have hC : HasRealParity (Polynomial.C c) 0 := hasRealParity_C c (by rfl)
  exact (hC.mul hP).congr (by omega)

theorem HasRealParity.square_even {P : ℝ[X]} {p : ℕ} (hP : HasRealParity P p) :
    HasRealParity (P ^ 2) 0 := by
  have hmul : HasRealParity (P * P) (p + p) := hP.mul hP
  rw [pow_two]
  exact hmul.congr (by omega)

/-- The monomial `X^n` has parity `n`. -/
theorem hasRealParity_X_pow (n : ℕ) :
    HasRealParity ((X : ℝ[X]) ^ n) n := by
  intro k hk
  rw [Polynomial.coeff_X_pow] at hk
  by_cases hkn : k = n
  · omega
  · simp [hkn] at hk

/-- The source factor `1 - X^2` is even. -/
theorem hasRealParity_one_sub_X_sq :
    HasRealParity ((1 : ℝ[X]) - X ^ 2) 0 := by
  exact (hasRealParity_one (by rfl)).sub
    ((hasRealParity_X_pow 2).congr (by omega))

/-- The factor `1 - X^2` has degree at most two. -/
theorem one_sub_X_sq_natDegree_le_two :
    (((1 : ℝ[X]) - X ^ 2).natDegree ≤ 2) := by
  have hone : (1 : ℝ[X]).natDegree ≤ 2 := by
    rw [Polynomial.natDegree_one]
    norm_num
  have hXsq : ((X : ℝ[X]) ^ 2).natDegree ≤ 2 := by
    rw [Polynomial.natDegree_X_pow]
  exact Polynomial.natDegree_sub_le_of_le hone hXsq

/-- The interval square decomposition promised by [GSLW19,
BlockHam.tex:436-480]:

`A = B^2 + (1 - X^2) * C^2`.

The source proof also tracks degree and parity bounds; they are fields here so
later QSP/QSVT modules can consume the certificate without re-reading the root
classification proof. -/
abbrev Certificate (A : ℝ[X]) :=
  Complement.Interval.Certificate.SquareCertificate A

/-- The full degree/parity certificate promised by Gilyen--Su--Low--Wiebe
[GSLW19, BlockHam.tex:436-480].

The source writes `deg(C) <= k-1`; the Lean fields record the product-friendly
bound `deg(C) <= k` together with the opposite parity `k+1 (mod 2)`.  Together
these exclude a top-degree `k` term except for the zero boundary case, while
avoiding partial subtraction in downstream code. -/
abbrev DegreeParityCertificate (A : ℝ[X]) (k : ℕ) :=
  Complement.Interval.Certificate.DegreeParityCertificate A k

/-- Forget the degree/parity bounds when only nonnegativity is needed. -/
def DegreeParityCertificate.toCertificate {A : ℝ[X]} {k : ℕ}
    (h : DegreeParityCertificate A k) : Certificate A where
  B := h.B
  C := h.C
  eq_decomposition := h.eq_decomposition

namespace DegreeParityCertificate

/-- The zero polynomial is the trivial boundary case in
[GSLW19, BlockHam.tex:441]. -/
noncomputable def zero (k : ℕ) : DegreeParityCertificate (0 : ℝ[X]) k where
  B := 0
  C := 0
  eq_decomposition := by simp
  degree_B := by simp
  degree_C := by simp
  parity_B := hasRealParity_zero k
  parity_C := hasRealParity_zero (k + 1)

/-- A pure square has an interval-square degree/parity certificate with the
second square set to zero. -/
noncomputable def ofSquare {k : ℕ} (B : ℝ[X]) (hdeg : B.natDegree ≤ k)
    (hpar : HasRealParity B k) : DegreeParityCertificate (B ^ 2) k where
  B := B
  C := 0
  eq_decomposition := by simp
  degree_B := hdeg
  degree_C := by simp
  parity_B := hpar
  parity_C := hasRealParity_zero (k + 1)

/-- The unit polynomial is the empty-product degree/parity certificate. -/
noncomputable def one : DegreeParityCertificate (1 : ℝ[X]) 0 := by
  simpa using
    (ofSquare (k := 0) (1 : ℝ[X]) (by rw [Polynomial.natDegree_one])
      (hasRealParity_one (by rfl)))

end DegreeParityCertificate

/-- Squares have the interval-square form, with the second square zero.  This
is an elementary sanity check for the certificate API, not the Gilyén root-class
decomposition itself. -/
noncomputable def ofSquare (B : ℝ[X]) :
    Certificate (B ^ 2) where
  B := B
  C := 0
  eq_decomposition := by simp

/-- The unit polynomial has the interval-square form. -/
noncomputable def one : Certificate (1 : ℝ[X]) where
  B := 1
  C := 0
  eq_decomposition := by simp

/-- If a certificate is present, its stored equality can be used directly. -/
theorem eq_of_certificate {A : ℝ[X]} (h : Certificate A) :
    A = h.B ^ 2 + (1 - X ^ 2) * h.C ^ 2 :=
  h.eq_decomposition

/-- Any interval-square certificate proves nonnegativity on `[-1,1]`. -/
theorem nonnegativeOnUnitInterval_of_certificate {A : ℝ[X]} (h : Certificate A) :
    NonnegativeOnUnitInterval A := by
  intro x hx
  rw [h.eq_decomposition]
  have hx_nonneg : 0 ≤ 1 - x ^ 2 := by
    nlinarith [hx.1, hx.2]
  have hB : 0 ≤ (h.B.eval x) ^ 2 := sq_nonneg _
  have hC : 0 ≤ (h.C.eval x) ^ 2 := sq_nonneg _
  simp
  nlinarith [mul_nonneg hx_nonneg hC, hB]

namespace DegreeParityCertificate

/-- A degree/parity certificate in particular proves interval nonnegativity. -/
theorem nonnegativeOnUnitInterval {A : ℝ[X]} {k : ℕ}
    (h : DegreeParityCertificate A k) : NonnegativeOnUnitInterval A :=
  nonnegativeOnUnitInterval_of_certificate h.toCertificate

/-- The product-friendly `degree_C <= k` field and opposite parity recover the
source-style strict degree bound except in the zero boundary case. -/
theorem degree_C_source_bound {A : ℝ[X]} {k : ℕ}
    (h : DegreeParityCertificate A k) : h.C = 0 ∨ h.C.natDegree + 1 ≤ k := by
  by_cases hzero : h.C = 0
  · exact Or.inl hzero
  · right
    have hcoeff : h.C.coeff h.C.natDegree ≠ 0 := by
      simpa [Polynomial.coeff_natDegree] using
        (Polynomial.leadingCoeff_ne_zero.mpr hzero)
    have hpar := h.parity_C h.C.natDegree hcoeff
    have hne : h.C.natDegree ≠ k := by
      intro heq
      omega
    have hlt : h.C.natDegree < k := lt_of_le_of_ne h.degree_C hne
    omega

end DegreeParityCertificate

/-- A real polynomial bounded by one on `[-1,1]` makes `1 - P^2`
nonnegative on that interval. -/
theorem one_sub_sq_nonnegative_of_bounded {P : ℝ[X]}
    (hP : BoundedByOneOnUnitInterval P) :
    NonnegativeOnUnitInterval (1 - P ^ 2) := by
  intro x hx
  have hbound := hP x hx
  rw [abs_le] at hbound
  have hnonneg : 0 ≤ 1 - (P.eval x) ^ 2 := by
    nlinarith [hbound.1, hbound.2]
  simpa using hnonneg

/-! #### Source factor identities -/

/-- The real-root factor rearrangement from [GSLW19, BlockHam.tex:459-460].

For a real root class with representative `s`, the factor `s^2 - x^2`
is written as a sum of a square term and `(1 - x^2)` times another square
coefficient.  This is the polynomial identity behind the first displayed
factor `R_(s)(x) R_(s)^*(x)`. -/
theorem realRootFactor_rearrangement (s x : ℝ) :
    s ^ 2 - x ^ 2 = (s ^ 2 - 1) * x ^ 2 + s ^ 2 * (1 - x ^ 2) := by
  ring

/-- The imaginary-root factor rearrangement from [GSLW19,
BlockHam.tex:461].

The source writes this as `x^2 + |s|^2`; here `r` denotes the nonnegative
real number `|s|`, but the algebraic identity itself does not need the
nonnegativity hypothesis. -/
theorem imaginaryRootFactor_rearrangement (r x : ℝ) :
    x ^ 2 + r ^ 2 = (r ^ 2 + 1) * x ^ 2 + r ^ 2 * (1 - x ^ 2) := by
  ring

/-- The complex linear factors for the real root pair `±s` multiply to the
complexification of `x^2-s^2`, matching the real-root grouping step of
[GSLW19, BlockHam.tex:450-456]. -/
theorem complexLinearFactors_realPair (s : ℝ) :
    (X - Polynomial.C (s : ℂ)) *
        (X - Polynomial.C ((-s : ℝ) : ℂ)) =
      realPolynomialToComplex ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) := by
  apply Polynomial.funext
  intro z
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow]
  ring

/-- The paired interior-real-root source factor corresponds to two copies of
the real pair of complex linear factors [GSLW19, BlockHam.tex:445,469-474]. -/
theorem complexLinearFactors_interiorRealPair (s : ℝ) :
    ((X - Polynomial.C (s : ℂ)) *
        (X - Polynomial.C ((-s : ℝ) : ℂ))) ^ 2 =
      realPolynomialToComplex
        (((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2) := by
  rw [complexLinearFactors_realPair, realPolynomialToComplex_pow]

/-- The outside-real-root source factor `s^2-x^2` differs from the complex
linear pair product by the expected sign [GSLW19, BlockHam.tex:459-460]. -/
theorem realPolynomialToComplex_outsideRealFactor (s : ℝ) :
    realPolynomialToComplex (Polynomial.C (s ^ 2) - (X : ℝ[X]) ^ 2) =
      -((X - Polynomial.C (s : ℂ)) *
        (X - Polynomial.C ((-s : ℝ) : ℂ))) := by
  rw [complexLinearFactors_realPair]
  simp [realPolynomialToComplex_sub]

/-- The complex linear factors for the imaginary root pair `±ir` multiply to
the complexification of `x^2+r^2`, matching the source imaginary-root factor
[GSLW19, BlockHam.tex:461]. -/
theorem complexLinearFactors_imaginaryPair (r : ℝ) :
    (X - Polynomial.C (Complex.I * (r : ℂ))) *
        (X - Polynomial.C (-(Complex.I * (r : ℂ)))) =
      realPolynomialToComplex ((X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)) := by
  ring_nf
  have hC :
      -(Polynomial.C Complex.I * Polynomial.C (r : ℂ) *
          (Polynomial.C Complex.I * Polynomial.C (r : ℂ))) =
        Polynomial.C (r : ℂ) ^ 2 := by
    rw [(Polynomial.C_mul (R := ℂ) (a := Complex.I) (b := (r : ℂ))).symm]
    rw [(Polynomial.C_mul (R := ℂ) (a := Complex.I * (r : ℂ))
      (b := Complex.I * (r : ℂ))).symm]
    rw [show (Complex.I * (r : ℂ)) * (Complex.I * (r : ℂ)) =
        -((r : ℂ) ^ 2) by
      ring_nf
      rw [Complex.I_sq]
      ring]
    simp
  simpa using hC

/-- The complex linear factors for a non-real quartet
`a+ib, -(a+ib), a-ib, -(a-ib)` multiply to the source quartic factor
[GSLW19, BlockHam.tex:462-466]. -/
theorem complexLinearFactors_complexQuartet (a b : ℝ) :
    ((X - Polynomial.C ((a : ℂ) + Complex.I * (b : ℂ))) *
        (X - Polynomial.C (-((a : ℂ) + Complex.I * (b : ℂ))))) *
      ((X - Polynomial.C ((a : ℂ) - Complex.I * (b : ℂ))) *
        (X - Polynomial.C (-((a : ℂ) - Complex.I * (b : ℂ))))) =
      realPolynomialToComplex
        ((X : ℝ[X]) ^ 4 + Polynomial.C (2 * (b ^ 2 - a ^ 2)) * X ^ 2 +
          Polynomial.C ((a ^ 2 + b ^ 2) ^ 2)) := by
  apply Polynomial.funext
  intro z
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow]
  ring_nf
  norm_num [Complex.I_sq]

/-- The quartet orbit product notation matches the source's non-real root
quartic factor [GSLW19, BlockHam.tex:450-456,462-466]. -/
theorem complexRootOrbit_linearFactorProduct (a b : ℝ) :
    ((complexRootOrbit ((a : ℂ) + Complex.I * (b : ℂ))).map
        (fun z => (X : ℂ[X]) - Polynomial.C z)).prod =
      realPolynomialToComplex
        ((X : ℝ[X]) ^ 4 + Polynomial.C (2 * (b ^ 2 - a ^ 2)) * X ^ 2 +
          Polynomial.C ((a ^ 2 + b ^ 2) ^ 2)) := by
  apply Polynomial.funext
  intro z
  simp [complexRootOrbit, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_pow, map_sub]
  ring_nf
  norm_num [Complex.I_sq]

/-- Complexification of the product of paired interior-real source factors.
This is the list-level form of [GSLW19, BlockHam.tex:452-454]. -/
theorem realPolynomialToComplex_product_interiorRealRootPair :
    ∀ roots : List ℝ,
      realPolynomialToComplex
          ((roots.map fun s => (((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2)).prod) =
        (roots.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod
  | [] => by simp
  | s :: roots => by
      simp only [List.map_cons, List.prod_cons]
      have hfactor :
          realPolynomialToComplex (((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2) =
            (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2 := by
        simpa using (complexLinearFactors_interiorRealPair s).symm
      rw [realPolynomialToComplex_mul,
        realPolynomialToComplex_product_interiorRealRootPair roots, hfactor]

/-- Complexification of the outside-real source factors, including the sign
change between `(x-s)(x+s)` and `s^2-x^2` [GSLW19, BlockHam.tex:453-460]. -/
theorem realPolynomialToComplex_product_outsideRealRoot :
    ∀ roots : List ℝ,
      realPolynomialToComplex
          ((roots.map fun s => Polynomial.C (s ^ 2) - (X : ℝ[X]) ^ 2).prod) =
        (roots.map fun s : ℝ =>
          -(((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ))))).prod
  | [] => by simp
  | s :: roots => by
      simp only [List.map_cons, List.prod_cons]
      have hfactor :
          realPolynomialToComplex (Polynomial.C (s ^ 2) - (X : ℝ[X]) ^ 2) =
            -(((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) := by
        simpa using realPolynomialToComplex_outsideRealFactor s
      rw [realPolynomialToComplex_mul,
        realPolynomialToComplex_product_outsideRealRoot roots, hfactor]

/-- Complexification of the source pure-imaginary factors
[GSLW19, BlockHam.tex:455,461]. -/
theorem realPolynomialToComplex_product_imaginaryRoot :
    ∀ roots : List ℝ,
      realPolynomialToComplex
          ((roots.map fun r => (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod) =
        (roots.map fun r : ℝ =>
          ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod
  | [] => by simp
  | r :: roots => by
      simp only [List.map_cons, List.prod_cons]
      have hfactor :
          realPolynomialToComplex ((X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)) =
            ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
              ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ)))) := by
        simpa using (complexLinearFactors_imaginaryPair r).symm
      rw [realPolynomialToComplex_mul,
        realPolynomialToComplex_product_imaginaryRoot roots, hfactor]

/-- Complexification of the source non-real-quartet factors
[GSLW19, BlockHam.tex:455-456,462-466]. -/
theorem realPolynomialToComplex_product_complexRoot :
    ∀ roots : List (ℝ × ℝ),
      realPolynomialToComplex
          ((roots.map fun z =>
            (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
              Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod) =
        (roots.map fun z : ℝ × ℝ =>
          ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod
  | [] => by simp
  | z :: roots => by
      simp only [List.map_cons, List.prod_cons]
      rw [realPolynomialToComplex_mul,
        realPolynomialToComplex_product_complexRoot roots,
        ← complexRootOrbit_linearFactorProduct z.1 z.2]

/-- Certificate constructor for a real-root factor outside the unit interval
[GSLW19, BlockHam.tex:459-460].  The hypothesis `1 <= s^2` is the algebraic
form of `|s| >= 1`. -/
noncomputable def realRootFactorCertificate (s : ℝ) (hs : 1 ≤ s ^ 2) :
    Certificate (Polynomial.C (s ^ 2) - X ^ 2) where
  B := Polynomial.C (Real.sqrt (s ^ 2 - 1)) * X
  C := Polynomial.C s
  eq_decomposition := by
    apply Polynomial.funext
    intro x
    have hsqrt : (Real.sqrt (s ^ 2 - 1)) ^ 2 = s ^ 2 - 1 := by
      exact Real.sq_sqrt (sub_nonneg.mpr hs)
    simp only [map_pow, eval_sub, eval_pow, eval_C, eval_X, eval_add, eval_mul,
      eval_one]
    rw [mul_pow, hsqrt]
    ring

/-- Certificate constructor for an imaginary-root pair factor [GSLW19,
BlockHam.tex:461].  The source writes the parameter as `|s|`; here it is the
real number `r`. -/
noncomputable def imaginaryRootFactorCertificate (r : ℝ) :
    Certificate (X ^ 2 + Polynomial.C (r ^ 2)) where
  B := Polynomial.C (Real.sqrt (r ^ 2 + 1)) * X
  C := Polynomial.C r
  eq_decomposition := by
    apply Polynomial.funext
    intro x
    have hsqrt : (Real.sqrt (r ^ 2 + 1)) ^ 2 = r ^ 2 + 1 := by
      exact Real.sq_sqrt (by nlinarith [sq_nonneg r])
    simp only [map_pow, eval_add, eval_pow, eval_X, eval_C, eval_mul, eval_sub,
      eval_one]
    rw [mul_pow, hsqrt]
    ring

/-- Radicand used in the complex-root factor `Q_(a,b)` of [GSLW19,
BlockHam.tex:462-466]. -/
def complexRootRadicand (a b : ℝ) : ℝ :=
  2 * (a ^ 2 + 1) * b ^ 2 + (a ^ 2 - 1) ^ 2 + b ^ 4

/-- The real parameter `c` used in the complex-root factor `Q_(a,b)` of
[GSLW19, BlockHam.tex:462-466]. -/
noncomputable def complexRootParameter (a b : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + Real.sqrt (complexRootRadicand a b)

/-- Algebraic condition on `c` that makes the complex-root quartic factor
split as `Q_(a,b)(x) Q_(a,b)^*(x)`. -/
def IsComplexRootParameter (a b c : ℝ) : Prop :=
  c ^ 2 - 1 - 2 * c * (a ^ 2 + b ^ 2) = 2 * (b ^ 2 - a ^ 2)

/-- The parameter specified in [GSLW19, BlockHam.tex:464-466] satisfies the
coefficient equation needed by the quartic factorization. -/
theorem complexRootParameter_isComplexRootParameter (a b : ℝ) :
    IsComplexRootParameter a b (complexRootParameter a b) := by
  have hrad_nonneg : 0 ≤ complexRootRadicand a b := by
    unfold complexRootRadicand
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a ^ 2 - 1), sq_nonneg (b ^ 2)]
  have hsqrt :
      (Real.sqrt (complexRootRadicand a b)) ^ 2 = complexRootRadicand a b := by
    simpa [sq] using Real.sq_sqrt hrad_nonneg
  unfold IsComplexRootParameter complexRootParameter
  set r : ℝ := Real.sqrt (complexRootRadicand a b) with hrdef
  have hr : r ^ 2 = complexRootRadicand a b := by
    simpa [hrdef] using hsqrt
  unfold complexRootRadicand at hr
  nlinarith [hr]

/-- The complex-root quartic factor rearrangement from [GSLW19,
BlockHam.tex:462-466], stated with the coefficient relation on `c` exposed.

The next theorem instantiates `c` with the source's square-root expression. -/
theorem complexRootFactor_rearrangement_of_parameter {a b c x : ℝ}
    (hc : IsComplexRootParameter a b c) :
    x ^ 4 + 2 * x ^ 2 * (b ^ 2 - a ^ 2) + (a ^ 2 + b ^ 2) ^ 2 =
      (c * x ^ 2 - (a ^ 2 + b ^ 2)) ^ 2 + (c ^ 2 - 1) * x ^ 2 * (1 - x ^ 2) := by
  unfold IsComplexRootParameter at hc
  nlinarith [hc]

/-- The complex-root quartic factor rearrangement using the explicit
parameter from [GSLW19, BlockHam.tex:462-466]. -/
theorem complexRootFactor_rearrangement (a b : ℝ) :
    ∀ x : ℝ,
      x ^ 4 + 2 * x ^ 2 * (b ^ 2 - a ^ 2) + (a ^ 2 + b ^ 2) ^ 2 =
        ((complexRootParameter a b) * x ^ 2 - (a ^ 2 + b ^ 2)) ^ 2 +
          ((complexRootParameter a b) ^ 2 - 1) * x ^ 2 * (1 - x ^ 2) := by
  intro x
  exact complexRootFactor_rearrangement_of_parameter
    (x := x) (complexRootParameter_isComplexRootParameter a b)

/-- The explicit complex-root parameter from [GSLW19, BlockHam.tex:464-466]
has `1 <= c^2`, so the coefficient `sqrt(c^2-1)` is real. -/
theorem complexRootParameter_sq_ge_one (a b : ℝ) :
    1 ≤ (complexRootParameter a b) ^ 2 := by
  have hrad_ge : (a ^ 2 - 1) ^ 2 ≤ complexRootRadicand a b := by
    unfold complexRootRadicand
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (b ^ 2)]
  have habs_le : |a ^ 2 - 1| ≤ Real.sqrt (complexRootRadicand a b) :=
    Real.abs_le_sqrt hrad_ge
  have hbase : 1 ≤ a ^ 2 + b ^ 2 + |a ^ 2 - 1| := by
    by_cases ha : 1 ≤ a ^ 2
    · nlinarith [ha, sq_nonneg b, abs_nonneg (a ^ 2 - 1)]
    · have hle : a ^ 2 ≤ 1 := le_of_not_ge ha
      have habs : |a ^ 2 - 1| = 1 - a ^ 2 := by
        simpa [sub_eq_add_neg] using abs_of_nonpos (sub_nonpos.mpr hle)
      rw [habs]
      nlinarith [sq_nonneg b]
  have hc_ge : 1 ≤ complexRootParameter a b := by
    unfold complexRootParameter
    nlinarith [hbase, habs_le]
  nlinarith [hc_ge]

/-- Certificate constructor for the complex-root quartic factor [GSLW19,
BlockHam.tex:462-466], stated with the source's algebraic condition on `c`.
The nonnegativity hypothesis `1 <= c^2` is exactly what lets the second square
use the real coefficient `sqrt(c^2-1)`. -/
noncomputable def complexRootFactorCertificate (a b c : ℝ)
    (hc : IsComplexRootParameter a b c) (hc_nonneg : 1 ≤ c ^ 2) :
    Certificate
      (X ^ 4 + Polynomial.C (2 * (b ^ 2 - a ^ 2)) * X ^ 2 +
        Polynomial.C ((a ^ 2 + b ^ 2) ^ 2)) where
  B := Polynomial.C c * X ^ 2 - Polynomial.C (a ^ 2 + b ^ 2)
  C := Polynomial.C (Real.sqrt (c ^ 2 - 1)) * X
  eq_decomposition := by
    apply Polynomial.funext
    intro x
    have hsqrt : (Real.sqrt (c ^ 2 - 1)) ^ 2 = c ^ 2 - 1 := by
      exact Real.sq_sqrt (sub_nonneg.mpr hc_nonneg)
    simp only [map_mul, map_sub, map_pow, map_add, eval_add, eval_pow, eval_X,
      eval_mul, eval_C, eval_sub, eval_one]
    rw [mul_pow, hsqrt]
    nlinarith [complexRootFactor_rearrangement_of_parameter (x := x) hc]

/-- Certificate constructor for the complex-root quartic factor using the
explicit square-root parameter from [GSLW19, BlockHam.tex:464-466]. -/
noncomputable def complexRootFactorCertificateExplicit (a b : ℝ) :
    Certificate
      (X ^ 4 + Polynomial.C (2 * (b ^ 2 - a ^ 2)) * X ^ 2 +
        Polynomial.C ((a ^ 2 + b ^ 2) ^ 2)) :=
  complexRootFactorCertificate a b (complexRootParameter a b)
    (complexRootParameter_isComplexRootParameter a b)
    (complexRootParameter_sq_ge_one a b)

/-! #### `B + i sqrt(1 - x^2) C` forms -/

/-- The source form `B(x) + i sqrt(1-x^2) C(x)` from [GSLW19,
BlockHam.tex:475-476]. -/
noncomputable def intervalComplexForm (B C : ℝ[X]) (x : ℝ) : ℂ :=
  ((Polynomial.eval x B : ℝ) : ℂ) +
    Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ) * ((Polynomial.eval x C : ℝ) : ℂ)

/-- Product closure for the source forms `B + i sqrt(1-x^2) C`
[GSLW19, BlockHam.tex:475-476]. -/
theorem intervalComplexForm_mul (B₁ C₁ B₂ C₂ : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    intervalComplexForm B₁ C₁ x * intervalComplexForm B₂ C₂ x =
      intervalComplexForm
        (B₁ * B₂ - (1 - X ^ 2) * C₁ * C₂)
        (B₁ * C₂ + C₁ * B₂) x := by
  have hs : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ^ 2 =
      ((1 - x ^ 2 : ℝ) : ℂ) := by
    calc
      ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 :=
        sq_sqrt_one_sub_sq (x := x) hx
      _ = ((1 - x ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
  have hcast : ((1 - x ^ 2 : ℝ) : ℂ) = 1 - (x : ℂ) ^ 2 := by
    push_cast
    ring
  simp [intervalComplexForm]
  ring_nf
  rw [hs, hcast, Complex.I_sq]
  ring_nf

/-- The product closure preserves the real-polynomial coefficient pair used by
the source proof. -/
noncomputable def mulFormLeft (B₁ C₁ B₂ C₂ : ℝ[X]) : ℝ[X] :=
  B₁ * B₂ - (1 - X ^ 2) * C₁ * C₂

/-- The imaginary coefficient of the product closure from [GSLW19,
BlockHam.tex:475-476]. -/
noncomputable def mulFormRight (B₁ C₁ B₂ C₂ : ℝ[X]) : ℝ[X] :=
  B₁ * C₂ + C₁ * B₂

theorem intervalComplexForm_mul' (B₁ C₁ B₂ C₂ : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    intervalComplexForm B₁ C₁ x * intervalComplexForm B₂ C₂ x =
      intervalComplexForm (mulFormLeft B₁ C₁ B₂ C₂)
        (mulFormRight B₁ C₁ B₂ C₂) x := by
  simpa [mulFormLeft, mulFormRight] using
    intervalComplexForm_mul B₁ C₁ B₂ C₂ hx

/-- Product closure for interval-square certificates, the polynomial-level
version of the source form product [GSLW19, BlockHam.tex:475-476]. -/
noncomputable def Certificate.mul {A D : ℝ[X]} (hA : Certificate A)
    (hD : Certificate D) : Certificate (A * D) where
  B := mulFormLeft hA.B hA.C hD.B hD.C
  C := mulFormRight hA.B hA.C hD.B hD.C
  eq_decomposition := by
    let B₁ : ℝ[X] := hA.B
    let C₁ : ℝ[X] := hA.C
    let B₂ : ℝ[X] := hD.B
    let C₂ : ℝ[X] := hD.C
    have hA_eq : A = B₁ ^ 2 + (1 - X ^ 2) * C₁ ^ 2 := by
      simpa [B₁, C₁] using hA.eq_decomposition
    have hD_eq : D = B₂ ^ 2 + (1 - X ^ 2) * C₂ ^ 2 := by
      simpa [B₂, C₂] using hD.eq_decomposition
    change A * D =
      (mulFormLeft B₁ C₁ B₂ C₂) ^ 2 +
        (1 - X ^ 2) * (mulFormRight B₁ C₁ B₂ C₂) ^ 2
    rw [hA_eq, hD_eq]
    simp [mulFormLeft, mulFormRight]
    ring

namespace DegreeParityCertificate

/-- Product closure for the source degree/parity interval-square certificates.
This is the degree-aware version of the source product construction in
[GSLW19, BlockHam.tex:475-480]. -/
noncomputable def mul {A D : ℝ[X]} {k l : ℕ}
    (hA : DegreeParityCertificate A k) (hD : DegreeParityCertificate D l) :
    DegreeParityCertificate (A * D) (k + l) where
  B := mulFormLeft hA.B hA.C hD.B hD.C
  C := mulFormRight hA.B hA.C hD.B hD.C
  eq_decomposition := (Certificate.mul hA.toCertificate hD.toCertificate).eq_decomposition
  degree_B := by
    unfold mulFormLeft
    have hleft : (hA.B * hD.B).natDegree ≤ k + l :=
      Polynomial.natDegree_mul_le_of_le hA.degree_B hD.degree_B
    have hright :
        (((1 : ℝ[X]) - X ^ 2) * hA.C * hD.C).natDegree ≤ k + l := by
      rcases (degree_C_source_bound (A := A) (k := k) hA) with hAzero | hAdeg
      · simp [hAzero]
      rcases (degree_C_source_bound (A := D) (k := l) hD) with hDzero | hDdeg
      · simp [hDzero]
      have hfirst :
          (((1 : ℝ[X]) - X ^ 2) * hA.C).natDegree ≤ 2 + hA.C.natDegree :=
        Polynomial.natDegree_mul_le_of_le one_sub_X_sq_natDegree_le_two
          (le_rfl : hA.C.natDegree ≤ hA.C.natDegree)
      have hall :
          ((((1 : ℝ[X]) - X ^ 2) * hA.C) * hD.C).natDegree ≤
            (2 + hA.C.natDegree) + hD.C.natDegree :=
        Polynomial.natDegree_mul_le_of_le hfirst
          (le_rfl : hD.C.natDegree ≤ hD.C.natDegree)
      exact le_trans hall (by omega)
    exact (Polynomial.natDegree_sub_le_of_le
      (p := hA.B * hD.B)
      (q := ((1 : ℝ[X]) - X ^ 2) * hA.C * hD.C)
      (m := k + l) (n := k + l) hleft hright).trans (by simp)
  degree_C := by
    unfold mulFormRight
    have hleft : (hA.B * hD.C).natDegree ≤ k + l :=
      Polynomial.natDegree_mul_le_of_le hA.degree_B hD.degree_C
    have hright : (hA.C * hD.B).natDegree ≤ k + l :=
      Polynomial.natDegree_mul_le_of_le hA.degree_C hD.degree_B
    exact Polynomial.natDegree_add_le_of_degree_le
      (p := hA.B * hD.C) (q := hA.C * hD.B) (n := k + l) hleft hright
  parity_B := by
    unfold mulFormLeft
    have hleft : HasRealParity (hA.B * hD.B) (k + l) :=
      hA.parity_B.mul hD.parity_B
    have hright :
        HasRealParity (((1 : ℝ[X]) - X ^ 2) * hA.C * hD.C) (k + l) := by
      have hraw :
          HasRealParity (((1 : ℝ[X]) - X ^ 2) * hA.C * hD.C)
            ((0 + (k + 1)) + (l + 1)) :=
        (hasRealParity_one_sub_X_sq.mul hA.parity_C).mul hD.parity_C
      exact hraw.congr (by omega)
    exact hleft.sub hright
  parity_C := by
    unfold mulFormRight
    have hleft :
        HasRealParity (hA.B * hD.C) (k + l + 1) :=
      (hA.parity_B.mul hD.parity_C).congr (by omega)
    have hright :
        HasRealParity (hA.C * hD.B) (k + l + 1) :=
      (hA.parity_C.mul hD.parity_B).congr (by omega)
    exact hleft.add hright

end DegreeParityCertificate

/-- One source root-class factor together with its interval-square
certificate. -/
structure FactorCertificate where
  /-- Source root-class polynomial represented by this factor. -/
  poly : ℝ[X]
  /-- Interval-square certificate for `poly`. -/
  certificate : Certificate poly

namespace FactorCertificate

/-- Product polynomial represented by a list of source factors. -/
noncomputable def productPoly : List FactorCertificate → ℝ[X]
  | [] => 1
  | factor :: factors => factor.poly * productPoly factors

/-- Product closure for a list of source factor certificates [GSLW19,
BlockHam.tex:475-480]. -/
noncomputable def productCertificate :
    (factors : List FactorCertificate) → Certificate (productPoly factors)
  | [] => one
  | factor :: factors => Certificate.mul factor.certificate (productCertificate factors)

end FactorCertificate

/-- A source-style factorization of a polynomial into root-class factors that
already carry interval-square certificates.  This is the compact interface
between the root classification proof and the final interval-square
decomposition [GSLW19, BlockHam.tex:436-480]. -/
structure ProductDecomposition (A : ℝ[X]) where
  /-- Certified factors whose product represents `A`. -/
  factors : List FactorCertificate
  product_eq : A = FactorCertificate.productPoly factors

namespace ProductDecomposition

/-- A source product decomposition yields an interval-square certificate. -/
noncomputable def toCertificate {A : ℝ[X]} (h : ProductDecomposition A) :
    Certificate A :=
  let factors : List FactorCertificate := h.factors
  let cert := FactorCertificate.productCertificate factors
  { B := cert.B
    C := cert.C
    eq_decomposition := by
      have hprod : A = FactorCertificate.productPoly factors := by
        simpa [factors] using h.product_eq
      have hcert : FactorCertificate.productPoly factors =
          cert.B ^ 2 + (1 - X ^ 2) * cert.C ^ 2 := cert.eq_decomposition
      rw [hprod]
      exact hcert }

end ProductDecomposition

/-- One source root-class factor together with its degree contribution and
degree/parity certificate.  This is the product-ready interface for the root
classification in [GSLW19, BlockHam.tex:436-480]. -/
structure DegreeParityFactorCertificate where
  /-- Source root-class polynomial represented by this factor. -/
  poly : ℝ[X]
  /-- Degree contribution of this source factor. -/
  degree : ℕ
  /-- Degree/parity interval-square certificate for `poly`. -/
  certificate : DegreeParityCertificate poly degree

/-- A source real root outside the open unit interval, represented by the
positive representative `s` used in the source factor `s^2 - x^2`
[GSLW19, BlockHam.tex:446,453-460]. -/
structure OutsideRealRoot where
  /-- Nonnegative outside-interval representative used in `s^2 - X^2`. -/
  value : ℝ
  outside : 1 ≤ value ^ 2

theorem sq_ge_one_of_not_mem_Ioo (s : ℝ) (hs : s ∉ Set.Ioo (-1 : ℝ) 1) :
    1 ≤ s ^ 2 := by
  by_cases hleft : s ≤ -1
  · nlinarith
  · have hgt_left : -1 < s := lt_of_not_ge hleft
    have hge_right : 1 ≤ s := by
      exact le_of_not_gt (fun hlt_right => hs ⟨hgt_left, hlt_right⟩)
    nlinarith

namespace OutsideRealRoot

/-- Normalize an outside real root to the nonnegative representative used by
the source factor `s^2 - x^2` [GSLW19, BlockHam.tex:453-460]. -/
noncomputable def ofReal (s : ℝ) (hs : s ∉ Set.Ioo (-1 : ℝ) 1) :
    OutsideRealRoot where
  value := |s|
  outside := by
    simpa [sq_abs] using sq_ge_one_of_not_mem_Ioo s hs

end OutsideRealRoot

/-- Outside-real wrapper for the proof-carrying representatives used by the
source factorization [GSLW19, BlockHam.tex:453-460]. -/
theorem realPolynomialToComplex_product_outsideRealRoots :
    ∀ roots : List OutsideRealRoot,
      realPolynomialToComplex
          ((roots.map fun s => Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod) =
        (roots.map fun s : OutsideRealRoot =>
          -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod
  | [] => by simp
  | s :: roots => by
      simp only [List.map_cons, List.prod_cons]
      have hfactor :
          realPolynomialToComplex (Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2) =
            -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ)))) := by
        simpa using realPolynomialToComplex_outsideRealFactor s.value
      rw [realPolynomialToComplex_mul,
        realPolynomialToComplex_product_outsideRealRoots roots, hfactor]

/-- The source's outside-real factors contribute one sign per representative
when translated to complex linear factors [GSLW19, BlockHam.tex:453-460]. -/
theorem outsideRealRoots_negativeLinearFactorProduct
    (roots : List OutsideRealRoot) :
    (roots.map fun s : OutsideRealRoot =>
        -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
          ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod =
      (-1 : ℂ[X]) ^ roots.length *
        (roots.map fun s : OutsideRealRoot =>
          ((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ)))).prod := by
  simpa [Function.comp_def] using
    (List.prod_map_neg (roots.map fun s : OutsideRealRoot =>
      ((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
        ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ)))))

/-- Complexification of the full source product notation from
[GSLW19, BlockHam.tex:452-456].  This is the algebraic bridge used before the
root product is grouped into zero, real, imaginary, and quartet factors. -/
theorem realPolynomialToComplex_sourceProductNotation
    (constant : ℝ) (zeroRootPairs : ℕ) (interiorRoots : List ℝ)
    (outsideRoots : List OutsideRealRoot) (imaginaryRoots : List ℝ)
    (complexRoots : List (ℝ × ℝ)) :
    realPolynomialToComplex
        (Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * zeroRootPairs) *
          (interiorRoots.map fun s =>
            ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
          (outsideRoots.map fun s =>
            Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
          (imaginaryRoots.map fun r =>
            (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
          (complexRoots.map fun z =>
            (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
              Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod) =
      Polynomial.C (constant : ℂ) *
        (X : ℂ[X]) ^ (2 * zeroRootPairs) *
        (interiorRoots.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod *
        (outsideRoots.map fun s : OutsideRealRoot =>
          -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod *
        (imaginaryRoots.map fun r : ℝ =>
          ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod *
        (complexRoots.map fun z : ℝ × ℝ =>
          ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod := by
  rw [realPolynomialToComplex_mul, realPolynomialToComplex_mul,
    realPolynomialToComplex_mul, realPolynomialToComplex_mul,
    realPolynomialToComplex_mul]
  rw [realPolynomialToComplex_C, realPolynomialToComplex_pow,
    realPolynomialToComplex_X]
  rw [realPolynomialToComplex_product_interiorRealRootPair,
    realPolynomialToComplex_product_outsideRealRoots,
    realPolynomialToComplex_product_imaginaryRoot,
    realPolynomialToComplex_product_complexRoot]

namespace SourceRootProductData

/-- Outside real-root representatives repeated by multiplicity, carrying the
`1 <= s^2` proof required by the source factor `s^2 - x^2`
[GSLW19, BlockHam.tex:453-460]. -/
noncomputable def outsideRealRoots {A : ℝ[X]}
    (data : SourceRootProductData A) : List OutsideRealRoot :=
  data.positiveOutsideRealRootValues.attach.flatMap fun s =>
    let z : ℂ := s.1
    List.replicate ((realPolynomialToComplex A).rootMultiplicity z)
      { value := s.1
        outside := by
          have hs : 1 ≤ s.1 :=
            mem_positiveOutsideRealRootValues (data := data) s.2
          nlinarith }

/-- A proof-carrying outside-real representative is still a canonical complex
root. -/
theorem root_mem_of_mem_outsideRealRoots
    {A : ℝ[X]} {data : SourceRootProductData A} {s : OutsideRealRoot}
    (hs : s ∈ data.outsideRealRoots) :
    (s.value : ℂ) ∈ data.roots := by
  classical
  unfold outsideRealRoots at hs
  rcases List.mem_flatMap.mp hs with ⟨t, _ht, hsrep⟩
  have hseq : s =
      { value := t.1
        outside := by
          have ht : 1 ≤ t.1 :=
            mem_positiveOutsideRealRootValues (data := data) t.2
          nlinarith } := (List.mem_replicate.mp hsrep).2
  subst hseq
  exact root_mem_of_mem_positiveOutsideRealRootValues (data := data) t.2

/-- A proof-carrying outside-real representative keeps the positive
orientation of the selected source representative [GSLW19,
BlockHam.tex:453-460]. -/
theorem value_pos_of_mem_outsideRealRoots
    {A : ℝ[X]} {data : SourceRootProductData A} {s : OutsideRealRoot}
    (hs : s ∈ data.outsideRealRoots) : 0 < s.value := by
  classical
  unfold outsideRealRoots at hs
  rcases List.mem_flatMap.mp hs with ⟨t, _ht, hsrep⟩
  have hseq : s =
      { value := t.1
        outside := by
          have ht : 1 ≤ t.1 :=
            mem_positiveOutsideRealRootValues (data := data) t.2
          nlinarith } := (List.mem_replicate.mp hsrep).2
  have hvalue : s.value = t.1 := congrArg OutsideRealRoot.value hseq
  have ht : 1 ≤ t.1 :=
    mem_positiveOutsideRealRootValues (data := data) t.2
  linarith

/-- The proof-carrying outside-real-root list has the same length as the raw
multiplicity-expanded outside-real parameter list. -/
theorem length_outsideRealRoots {A : ℝ[X]} (data : SourceRootProductData A) :
    data.outsideRealRoots.length = data.outsideRealRootParameters.length := by
  simp [outsideRealRoots, outsideRealRootParameters, List.length_flatMap]

/-- Forgetting the proof component from the proof-carrying outside-real list
recovers the raw multiplicity-expanded outside-real parameters [GSLW19,
BlockHam.tex:446,453-460]. -/
theorem map_value_outsideRealRoots {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.outsideRealRoots.map fun s : OutsideRealRoot => s.value) =
      data.outsideRealRootParameters := by
  simp [outsideRealRoots, outsideRealRootParameters, List.map_flatMap]

/-- Expanded outside-real representatives multiply to the corresponding
two-point linear-factor products with full root multiplicity [GSLW19,
BlockHam.tex:446,453-460]. -/
theorem outsideRealRoot_linearFactorProduct
    {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.outsideRealRoots.map fun s : OutsideRealRoot =>
        ((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
          ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ)))).prod =
      (data.positiveOutsideRealRootValues.map fun s : ℝ =>
        (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
          ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
            (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod := by
  classical
  unfold outsideRealRoots
  simp only [List.map_flatMap, List.map_replicate]
  rw [list_prod_flatMap_replicate]
  simp

/-- The real scalar in the source product after absorbing the sign introduced
by outside-real factors `s^2-x^2` [GSLW19, BlockHam.tex:453-460]. -/
noncomputable def sourceConstant {A : ℝ[X]} (data : SourceRootProductData A) : ℝ :=
  (-1 : ℝ) ^ data.outsideRealRoots.length * A.leadingCoeff

/-- Multiplying the source constant by the outside-real sign recovers the
canonical leading coefficient after coefficient extension. -/
theorem sourceConstant_mul_outsideSign {A : ℝ[X]} (data : SourceRootProductData A) :
    Polynomial.C ((data.sourceConstant : ℝ) : ℂ) *
        ((-1 : ℂ[X]) ^ data.outsideRealRoots.length) =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff := by
  unfold sourceConstant
  rw [realPolynomialToComplex]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, map_mul, map_pow, map_neg, map_one, leadingCoeff_map,
    Complex.coe_algebraMap]
  have hsign :
      ((-1 : ℂ[X]) ^ data.outsideRealRoots.length) *
          ((-1 : ℂ[X]) ^ data.outsideRealRoots.length) = 1 := by
    rw [← pow_add]
    have hdouble :
        data.outsideRealRoots.length + data.outsideRealRoots.length =
          2 * data.outsideRealRoots.length := by omega
    rw [hdouble]
    simp [pow_mul]
  calc
    (-1 : ℂ[X]) ^ data.outsideRealRoots.length *
        Polynomial.C (A.leadingCoeff : ℂ) *
          (-1 : ℂ[X]) ^ data.outsideRealRoots.length =
        Polynomial.C (A.leadingCoeff : ℂ) *
          (((-1 : ℂ[X]) ^ data.outsideRealRoots.length) *
            ((-1 : ℂ[X]) ^ data.outsideRealRoots.length)) := by
      ring
    _ = Polynomial.C (A.leadingCoeff : ℂ) := by
      rw [hsign, mul_one]

/-- Number of zero-root pairs determined by the source evenness facts. -/
noncomputable def zeroRootPairs {A : ℝ[X]} (data : SourceRootProductData A) : ℕ :=
  data.facts.zeroRootPairCount

/-- The extracted zero-root pair count accounts for the full zero-root
multiplicity in the complexified source polynomial [GSLW19,
BlockHam.tex:442-452]. -/
theorem two_mul_zeroRootPairs {A : ℝ[X]} (data : SourceRootProductData A) :
    2 * data.zeroRootPairs =
      (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) := by
  exact data.facts.two_mul_zeroRootPairCount

/-- The zero-root class contributes the source factor `x^(2k)`, where `k` is
half of the zero-root multiplicity [GSLW19, BlockHam.tex:442-452]. -/
theorem zeroRootLinearFactorProduct {A : ℝ[X]} (data : SourceRootProductData A) :
    (((X : ℂ[X]) - Polynomial.C (0 : ℂ)) ^
        (realPolynomialToComplex A).rootMultiplicity (0 : ℂ)) =
      (X : ℂ[X]) ^ (2 * data.zeroRootPairs) := by
  rw [← data.two_mul_zeroRootPairs]
  simp

/-- The displayed source product, after coefficient extension, is the grouped
linear-factor product indexed by the selected source representatives
[GSLW19, BlockHam.tex:452-480].  The final root-product proof identifies this
grouped product with the canonical complex root product. -/
theorem realPolynomialToComplex_sourceProductNotation_grouped
    {A : ℝ[X]} (data : SourceRootProductData A) (constant : ℝ) :
    realPolynomialToComplex
        (Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          (data.interiorRealRootPairParameters.map fun s =>
            ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
          (data.outsideRealRoots.map fun s =>
            Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
          (data.imaginaryRootParameters.map fun r =>
            (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
          (data.complexRootParameters.map fun z =>
            (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
              Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod) =
      Polynomial.C (constant : ℂ) *
        (X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
        ((-1 : ℂ[X]) ^ data.outsideRealRoots.length *
          (data.positiveOutsideRealRootValues.map fun s : ℝ =>
            (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
                (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod) *
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
              (realPolynomialToComplex A).rootMultiplicity
                (Complex.I * (r : ℂ))).prod *
        (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (((complexRootOrbit z).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
              (realPolynomialToComplex A).rootMultiplicity z).prod := by
  rw [realPolynomialToComplex_sourceProductNotation]
  rw [data.interiorRealRootPair_linearFactorProduct]
  rw [outsideRealRoots_negativeLinearFactorProduct]
  rw [data.outsideRealRoot_linearFactorProduct]
  rw [data.imaginaryRoot_linearFactorProduct]
  rw [data.complexRoot_linearFactorProduct]

/-- The grouped source product with the sign-corrected source constant has the
same leading scalar as the canonical complex root product [GSLW19,
BlockHam.tex:453-480]. -/
theorem realPolynomialToComplex_sourceProductNotation_grouped_sourceConstant
    {A : ℝ[X]} (data : SourceRootProductData A) :
    realPolynomialToComplex
        (Polynomial.C data.sourceConstant *
          (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          (data.interiorRealRootPairParameters.map fun s =>
            ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
          (data.outsideRealRoots.map fun s =>
            Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
          (data.imaginaryRootParameters.map fun r =>
            (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
          (data.complexRootParameters.map fun z =>
            (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
              Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod) =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff *
        (X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
              (realPolynomialToComplex A).rootMultiplicity
                (Complex.I * (r : ℂ))).prod *
        (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (((complexRootOrbit z).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
              (realPolynomialToComplex A).rootMultiplicity z).prod := by
  rw [realPolynomialToComplex_sourceProductNotation_grouped]
  have hconst := data.sourceConstant_mul_outsideSign
  let Z : ℂ[X] := (X : ℂ[X]) ^ (2 * data.zeroRootPairs)
  let I : ℂ[X] :=
    (data.positiveInteriorRealRootValues.map fun s : ℝ =>
      (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
        ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod
  let O : ℂ[X] :=
    (data.positiveOutsideRealRootValues.map fun s : ℝ =>
      (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
        ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod
  let J : ℂ[X] :=
    (data.positiveImaginaryRootValues.map fun r : ℝ =>
      (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
        ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
          (realPolynomialToComplex A).rootMultiplicity
            (Complex.I * (r : ℂ))).prod
  let Q : ℂ[X] :=
    (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
      (((complexRootOrbit z).map
        (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
          (realPolynomialToComplex A).rootMultiplicity z).prod
  change
    Polynomial.C ((data.sourceConstant : ℝ) : ℂ) * Z * I *
          (((-1 : ℂ[X]) ^ data.outsideRealRoots.length) * O) * J * Q =
      Polynomial.C (realPolynomialToComplex A).leadingCoeff * Z * I * O * J * Q
  calc
    Polynomial.C ((data.sourceConstant : ℝ) : ℂ) * Z * I *
          (((-1 : ℂ[X]) ^ data.outsideRealRoots.length) * O) * J * Q =
        (Polynomial.C ((data.sourceConstant : ℝ) : ℂ) *
            ((-1 : ℂ[X]) ^ data.outsideRealRoots.length)) * Z * I * O * J * Q := by
      ring
    _ = Polynomial.C (realPolynomialToComplex A).leadingCoeff * Z * I * O * J * Q := by
      rw [hconst]

/-- The explicit grouped complex root list represented by the source product:
zero roots, paired real roots, paired imaginary roots, and non-real quartets
[GSLW19, BlockHam.tex:442-456]. -/
noncomputable def groupedRootList {A : ℝ[X]} (data : SourceRootProductData A) :
    List ℂ :=
  List.replicate (2 * data.zeroRootPairs) 0 ++
    data.interiorRealRootPairParameters.flatMap (fun s : ℝ =>
      [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)]) ++
    data.outsideRealRoots.flatMap (fun s : OutsideRealRoot =>
      [(s.value : ℂ), -(s.value : ℂ)]) ++
    data.imaginaryRootParameters.flatMap (fun r : ℝ =>
      [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))]) ++
    data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))

/-- Linear-factor product over `groupedRootList`, rewritten in the source
representative notation [GSLW19, BlockHam.tex:452-480]. -/
theorem groupedRootList_linearFactorProduct
    {A : ℝ[X]} (data : SourceRootProductData A) :
    (data.groupedRootList.map (fun z : ℂ => (X : ℂ[X]) - Polynomial.C z)).prod =
      (X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
              (realPolynomialToComplex A).rootMultiplicity
                (Complex.I * (r : ℂ))).prod *
        (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (((complexRootOrbit z).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
              (realPolynomialToComplex A).rootMultiplicity z).prod := by
  classical
  let factor : ℂ → ℂ[X] := fun z => (X : ℂ[X]) - Polynomial.C z
  have hzero :
      (List.map factor (List.replicate (2 * data.zeroRootPairs) (0 : ℂ))).prod =
        (X : ℂ[X]) ^ (2 * data.zeroRootPairs) := by
    simp [factor]
  have hinterior :
      (List.map factor
        (data.interiorRealRootPairParameters.flatMap (fun s : ℝ =>
          [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)]))).prod =
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod := by
    rw [List.map_flatMap]
    change
      (data.interiorRealRootPairParameters.flatMap fun s : ℝ =>
        [factor (s : ℂ), factor (-(s : ℂ)), factor (s : ℂ), factor (-(s : ℂ))]).prod =
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod
    rw [list_prod_flatMap_four_pair]
    simpa [factor] using data.interiorRealRootPair_linearFactorProduct
  have houtside :
      (List.map factor
        (data.outsideRealRoots.flatMap (fun s : OutsideRealRoot =>
          [(s.value : ℂ), -(s.value : ℂ)]))).prod =
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod := by
    rw [List.map_flatMap]
    change
      (data.outsideRealRoots.flatMap fun s : OutsideRealRoot =>
        [factor (s.value : ℂ), factor (-(s.value : ℂ))]).prod =
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
              (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod
    rw [list_prod_flatMap_two]
    simpa [factor] using data.outsideRealRoot_linearFactorProduct
  have himag :
      (List.map factor
        (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
          [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))]))).prod =
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
              (realPolynomialToComplex A).rootMultiplicity
                (Complex.I * (r : ℂ))).prod := by
    rw [List.map_flatMap]
    change
      (data.imaginaryRootParameters.flatMap fun r : ℝ =>
        [factor (Complex.I * (r : ℂ)), factor (-(Complex.I * (r : ℂ)))]).prod =
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
              (realPolynomialToComplex A).rootMultiplicity
                (Complex.I * (r : ℂ))).prod
    rw [list_prod_flatMap_two]
    simpa [factor] using data.imaginaryRoot_linearFactorProduct
  have hcomplex :
      (List.map factor
        (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
          complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))))).prod =
        (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (((complexRootOrbit z).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
              (realPolynomialToComplex A).rootMultiplicity z).prod := by
    rw [list_prod_map_flatMap]
    simpa [factor] using data.complexRoot_linearFactorProduct
  rw [SourceRootProductData.groupedRootList]
  simp only [List.map_append, List.prod_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]

/-- The zero-root class contributes no more than the canonical root multiset
cardinality.  This is the first summand of the source count
`2*rootClassDegree <= |S|` [GSLW19, BlockHam.tex:442-452,476-479]. -/
theorem SourceHypotheses.two_mul_zeroRootPairs_le_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    2 * (hA.rootProductData).zeroRootPairs ≤ (hA.rootProductData).roots.card := by
  calc
    2 * (hA.rootProductData).zeroRootPairs =
        (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) :=
      (hA.rootProductData).two_mul_zeroRootPairs
    _ = (hA.rootProductData).roots.count (0 : ℂ) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (0 : ℂ)).symm
    _ ≤ (hA.rootProductData).roots.card := by
      exact Multiset.count_le_card (0 : ℂ) (hA.rootProductData).roots

/-- Degree contribution of the root classes already selected from the complex
root multiset.  The final source count adds unit-padding factors to reach the
requested index `k` [GSLW19, BlockHam.tex:469-480]. -/
noncomputable def rootClassDegree {A : ℝ[X]} (data : SourceRootProductData A) : ℕ :=
  data.zeroRootPairs + 2 * data.interiorRealRootPairParameters.length +
    data.outsideRealRoots.length + data.imaginaryRootParameters.length +
      2 * data.complexRootParameters.length

/-- Expanded multiplicity-sum form of `rootClassDegree`.  This is the
bookkeeping bridge from the source root classes to the degree bound in
[GSLW19, BlockHam.tex:469-480]. -/
theorem rootClassDegree_eq_multiplicity_sums {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.rootClassDegree =
      data.zeroRootPairs +
        2 *
          (data.positiveInteriorRealRootValues.map fun s : ℝ =>
            (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum +
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
            (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum +
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
            (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum +
        2 *
          (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
            (realPolynomialToComplex A).rootMultiplicity z).sum := by
  rw [rootClassDegree, length_interiorRealRootPairParameters,
    length_outsideRealRoots, length_outsideRealRootParameters,
    length_imaginaryRootParameters, length_complexRootParameters]

end SourceRootProductData

/-- Once the source root classes have been counted inside the canonical root
multiset, the degree bound `rootClassDegree <= k` follows from
`|S| <= 2k` [GSLW19, BlockHam.tex:476-479]. -/
theorem SourceHypotheses.rootClassDegree_le_of_two_mul_le_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    (hcount :
      2 * (hA.rootProductData).rootClassDegree ≤ (hA.rootProductData).roots.card) :
    (hA.rootProductData).rootClassDegree ≤ k := by
  have hcard := hA.rootProductData_roots_card_le_two_mul
  omega

/-- The selected root-class degree is exactly half of the weighted source
root-class count: zero roots count once, real and imaginary two-point orbits
count twice, and first-quadrant quartets count four times. -/
theorem SourceHypotheses.two_mul_rootClassDegree_eq_weighted_countP
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    2 * (hA.rootProductData).rootClassDegree =
      (hA.rootProductData).roots.count (0 : ℂ) +
        2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots +
        2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots +
        2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots +
        4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots := by
  classical
  let data := hA.rootProductData
  let interior :=
    (data.positiveInteriorRealRootValues.map fun s : ℝ =>
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum
  let outside :=
    (data.positiveOutsideRealRootValues.map fun s : ℝ =>
      (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum
  let imaginary :=
    (data.positiveImaginaryRootValues.map fun r : ℝ =>
      (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum
  let complex :=
    (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
      (realPolynomialToComplex A).rootMultiplicity z).sum
  have hroot :
      data.rootClassDegree =
        data.zeroRootPairs + 2 * interior + outside + imaginary + 2 * complex := by
    simpa [data, interior, outside, imaginary, complex] using
      (SourceRootProductData.rootClassDegree_eq_multiplicity_sums
        (A := A) hA.rootProductData)
  have hzero :
      2 * data.zeroRootPairs = data.roots.count (0 : ℂ) := by
    calc
      2 * data.zeroRootPairs =
          (realPolynomialToComplex A).rootMultiplicity (0 : ℂ) := by
        simpa [data] using (hA.rootProductData).two_mul_zeroRootPairs
      _ = data.roots.count (0 : ℂ) := by
        simpa [data] using (hA.rootProductData_count_eq_rootMultiplicity (0 : ℂ)).symm
  have hint :
      2 * interior =
        @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) data.roots := by
    simpa [data, interior] using hA.two_mul_sum_half_positiveInterior_eq_countP
  have hout :
      outside =
        @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) data.roots := by
    simpa [data, outside] using hA.sum_rootMultiplicity_positiveOutside_eq_countP
  have himag :
      imaginary =
        @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) data.roots := by
    simpa [data, imaginary] using hA.sum_rootMultiplicity_positiveImaginary_eq_countP
  have hcomplex :
      complex =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
    simpa [data, complex] using hA.sum_rootMultiplicity_firstQuadrant_eq_countP
  rw [hroot]
  simp [data] at hzero hint hout himag hcomplex ⊢
  omega

/-- The source root classes form a disjoint partition of the complex root
multiset, so their weighted count is the multiset cardinality [GSLW19,
BlockHam.tex:442-456,476-479]. -/
theorem SourceHypotheses.weighted_sourceRootClass_count_eq_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).roots.count (0 : ℂ) +
        2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots +
        2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots +
        2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots +
        4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots =
      (hA.rootProductData).roots.card := by
  classical
  let roots := (hA.rootProductData).roots
  have hmember :
      @Multiset.countP ℂ IsSourceRootClassMember
          (fun z => Classical.propDecidable (IsSourceRootClassMember z)) roots =
        roots.card := by
    rw [Multiset.countP_eq_card]
    intro z _hz
    exact sourceRootClassMember_exhaustive z
  have hsplit :
      @Multiset.countP ℂ IsSourceRootClassMember
          (fun z => Classical.propDecidable (IsSourceRootClassMember z)) roots =
        @Multiset.countP ℂ (fun z => z = 0)
          (fun z => Classical.propDecidable (z = 0)) roots +
        @Multiset.countP ℂ IsInteriorRealRootClass
          (fun z => Classical.propDecidable (IsInteriorRealRootClass z)) roots +
        @Multiset.countP ℂ IsOutsideRealRootClass
          (fun z => Classical.propDecidable (IsOutsideRealRootClass z)) roots +
        @Multiset.countP ℂ IsImaginaryRootClass
          (fun z => Classical.propDecidable (IsImaginaryRootClass z)) roots +
        @Multiset.countP ℂ IsComplexQuartetRootClass
          (fun z => Classical.propDecidable (IsComplexQuartetRootClass z)) roots := by
    calc
      @Multiset.countP ℂ IsSourceRootClassMember
          (fun z => Classical.propDecidable (IsSourceRootClassMember z)) roots =
          @Multiset.countP ℂ (fun z =>
            z = 0 ∨ IsInteriorRealRootClass z ∨ IsOutsideRealRootClass z ∨
              IsImaginaryRootClass z ∨ IsComplexQuartetRootClass z)
            (fun z => Classical.propDecidable
              (z = 0 ∨ IsInteriorRealRootClass z ∨ IsOutsideRealRootClass z ∨
                IsImaginaryRootClass z ∨ IsComplexQuartetRootClass z)) roots := by
        exact multiset_countP_congr_iff roots (fun z => by
          simp [IsSourceRootClassMember])
      _ =
        @Multiset.countP ℂ (fun z => z = 0)
          (fun z => Classical.propDecidable (z = 0)) roots +
        @Multiset.countP ℂ IsInteriorRealRootClass
          (fun z => Classical.propDecidable (IsInteriorRealRootClass z)) roots +
        @Multiset.countP ℂ IsOutsideRealRootClass
          (fun z => Classical.propDecidable (IsOutsideRealRootClass z)) roots +
        @Multiset.countP ℂ IsImaginaryRootClass
          (fun z => Classical.propDecidable (IsImaginaryRootClass z)) roots +
        @Multiset.countP ℂ IsComplexQuartetRootClass
          (fun z => Classical.propDecidable (IsComplexQuartetRootClass z)) roots := by
        exact multiset_countP_or5_eq_add roots
          (fun z hzero hclass => by
            subst z
            simpa [IsInteriorRealRootClass] using hclass.2.1)
          (fun z hzero hclass => by
            subst z
            have hbad : (1 : ℝ) ≤ 0 := by
              simpa [IsOutsideRealRootClass] using hclass.2
            linarith)
          (fun z hzero hclass => by
            subst z
            simpa [IsImaginaryRootClass] using hclass.2)
          (fun z hzero hclass => by
            subst z
            exact hclass.1 (by simp))
          (fun z hinterior houtside => by
            linarith [hinterior.2.2, houtside.2])
          (fun z hinterior himag => by
            have hbad : 0 < |z.im| := himag.2
            simp [hinterior.1] at hbad)
          (fun z hinterior hcomplex => hcomplex.2 hinterior.1)
          (fun z houtside himag => by
            have hbad : 0 < |z.im| := himag.2
            simp [houtside.1] at hbad)
          (fun z houtside hcomplex => hcomplex.2 houtside.1)
          (fun z himag hcomplex => hcomplex.1 himag.1)
  have hzero :
      @Multiset.countP ℂ (fun z => z = 0)
          (fun z => Classical.propDecidable (z = 0)) roots =
        roots.count (0 : ℂ) := by
    simpa [Multiset.count] using
      (multiset_countP_congr_iff (s := roots)
        (p := fun z : ℂ => z = 0) (q := fun z : ℂ => 0 = z)
        (fun z => by
          constructor <;> intro hz <;> exact hz.symm))
  rw [hsplit, hzero,
    hA.countP_interiorRealRootClass_eq_two_mul_countP_positiveInterior,
    hA.countP_outsideRealRootClass_eq_two_mul_countP_positiveOutside,
    hA.countP_imaginaryRootClass_eq_two_mul_countP_positiveImaginary,
    hA.countP_complexQuartetRootClass_eq_four_mul_countP_firstQuadrant] at hmember
  simpa [roots] using hmember

/-- The selected source root-class degree consumes at most the available complex
roots [GSLW19, BlockHam.tex:476-479]. -/
theorem SourceHypotheses.two_mul_rootClassDegree_le_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    2 * (hA.rootProductData).rootClassDegree ≤ (hA.rootProductData).roots.card := by
  calc
    2 * (hA.rootProductData).rootClassDegree =
        (hA.rootProductData).roots.count (0 : ℂ) +
          2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots +
          2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots +
          2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots +
          4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
            (fun z => Classical.propDecidable
              (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots :=
      hA.two_mul_rootClassDegree_eq_weighted_countP
    _ = (hA.rootProductData).roots.card :=
      hA.weighted_sourceRootClass_count_eq_roots_card
    _ ≤ (hA.rootProductData).roots.card := le_rfl

/-- Exact root-count form of the selected source root classes.  The degree-bound
wrapper above uses only the `<=` direction, but product grouping also needs the
equality [GSLW19, BlockHam.tex:476-479]. -/
theorem SourceHypotheses.two_mul_rootClassDegree_eq_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    2 * (hA.rootProductData).rootClassDegree = (hA.rootProductData).roots.card := by
  calc
    2 * (hA.rootProductData).rootClassDegree =
        (hA.rootProductData).roots.count (0 : ℂ) +
          2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveInteriorRealRootRepresentative z)) (hA.rootProductData).roots +
          2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveOutsideRealRootRepresentative z)) (hA.rootProductData).roots +
          2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
            (fun z => Classical.propDecidable
              (IsPositiveImaginaryRootRepresentative z)) (hA.rootProductData).roots +
          4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
            (fun z => Classical.propDecidable
              (IsFirstQuadrantComplexRootRepresentative z)) (hA.rootProductData).roots :=
      hA.two_mul_rootClassDegree_eq_weighted_countP
    _ = (hA.rootProductData).roots.card :=
      hA.weighted_sourceRootClass_count_eq_roots_card

/-- The grouped root list has the same cardinality as the canonical root
multiset [GSLW19, BlockHam.tex:476-479]. -/
theorem SourceHypotheses.groupedRootList_length_eq_roots_card
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).groupedRootList.length =
      (hA.rootProductData).roots.card := by
  rw [← hA.two_mul_rootClassDegree_eq_roots_card]
  simp [SourceRootProductData.groupedRootList, complexRootOrbit,
    SourceRootProductData.rootClassDegree, List.length_flatMap]
  omega

/-- The grouped source root list has exactly the canonical multiplicity at the
zero-root class [GSLW19, BlockHam.tex:442-452]. -/
theorem SourceHypotheses.groupedRootList_count_zero
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).groupedRootList.count (0 : ℂ) =
      (hA.rootProductData).roots.count (0 : ℂ) := by
  classical
  let data := hA.rootProductData
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun s : ℝ =>
        [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)])).count (0 : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hz
    rcases List.mem_flatMap.mp hz with ⟨s, hs, hzmem⟩
    have hspos : 0 < s :=
      (SourceRootProductData.mem_interiorRealRootPairParameters
        (data := data) hs).1.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with hzero | hzero | hzero | hzero
    · have hs0 : s = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero.symm
      linarith
    · have hs0 : s = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero
      linarith
    · have hs0 : s = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero.symm
      linarith
    · have hs0 : s = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun s : OutsideRealRoot =>
        [(s.value : ℂ), -(s.value : ℂ)])).count (0 : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hz
    rcases List.mem_flatMap.mp hz with ⟨s, _hs, hzmem⟩
    have hsout : 1 ≤ s.value ^ 2 := s.outside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with hzero | hzero
    · have hs0 : s.value = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero.symm
      nlinarith
    · have hs0 : s.value = 0 := by
        apply Complex.ofReal_injective
        simpa using hzero
      nlinarith
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (0 : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hz
    rcases List.mem_flatMap.mp hz with ⟨r, hr, hzmem⟩
    have hrpos : 0 < r :=
      (SourceRootProductData.mem_imaginaryRootParameters
        (data := data) hr).1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with hzero | hzero
    all_goals
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (0 : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hz
    rcases List.mem_flatMap.mp hz with ⟨w, hw, hzmem⟩
    have hwpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hw).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with hzero | hzero | hzero | hzero
    all_goals
      have him := congrArg Complex.im hzero
      simp at him
      linarith
  simp [SourceRootProductData.groupedRootList, data, hinterior, houtside,
    himag, hcomplex, hA.rootProductData_count_eq_rootMultiplicity,
    SourceRootProductData.two_mul_zeroRootPairs]

/-- Equivalent zero-root count phrased in the source product parameter
`zeroRootPairs` [GSLW19, BlockHam.tex:442-452]. -/
theorem SourceHypotheses.groupedRootList_count_zero_eq_two_mul_zeroRootPairs
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData).groupedRootList.count (0 : ℂ) =
      2 * (hA.rootProductData).zeroRootPairs := by
  rw [hA.groupedRootList_count_zero,
    (hA.rootProductData).two_mul_zeroRootPairs,
    hA.rootProductData_count_eq_rootMultiplicity]

/-- The grouped interior-real block has the same cardinality as the canonical
interior-real root class [GSLW19, BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.interiorGroupedBlock_length_eq_countP_interior
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData.interiorRealRootPairParameters.flatMap (fun s : ℝ =>
      [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)])).length =
      @Multiset.countP ℂ IsInteriorRealRootClass
        (fun z => Classical.propDecidable (IsInteriorRealRootClass z))
        (hA.rootProductData).roots := by
  classical
  let data := hA.rootProductData
  have hlen :
      (data.interiorRealRootPairParameters.flatMap (fun s : ℝ =>
        [(s : ℂ), -(s : ℂ), (s : ℂ), -(s : ℂ)])).length =
        4 * data.interiorRealRootPairParameters.length := by
    simp [List.length_flatMap, Nat.mul_comm]
  have hparams :
      data.interiorRealRootPairParameters.length =
        (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum := by
    simpa [data] using
      SourceRootProductData.length_interiorRealRootPairParameters
        (A := A) hA.rootProductData
  have hpositive :
      2 * (data.positiveInteriorRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2).sum =
        @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) data.roots := by
    simpa [data] using hA.two_mul_sum_half_positiveInterior_eq_countP
  have hclass :
      @Multiset.countP ℂ IsInteriorRealRootClass
        (fun z => Classical.propDecidable (IsInteriorRealRootClass z))
        data.roots =
        2 * @Multiset.countP ℂ IsPositiveInteriorRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveInteriorRealRootRepresentative z)) data.roots := by
    simpa [data] using hA.countP_interiorRealRootClass_eq_two_mul_countP_positiveInterior
  rw [hlen, hparams, hclass]
  omega

/-- For a selected positive interior real root, the grouped source block has
exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.interiorGroupedBlock_count_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveInteriorRealRootValues) :
    (hA.rootProductData.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
      [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (s : ℂ) =
      hA.rootProductData.roots.count (s : ℂ) := by
  classical
  let data := hA.rootProductData
  have hscond : 0 < s ∧ s < 1 :=
    SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := data) hs
  have hparams_pos :
      ∀ t ∈ data.interiorRealRootPairParameters, 0 < t := by
    intro t ht
    exact (SourceRootProductData.mem_interiorRealRootPairParameters
      (data := data) ht).1.1
  have hblock :=
    list_count_flatMap_real_four_orbit
      data.interiorRealRootPairParameters s hparams_pos hscond.1
  have hparams :=
    SourceRootProductData.count_interiorRealRootPairParameters
      (A := A) (data := data) hs
  calc
    (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
      [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (s : ℂ) =
        2 * data.interiorRealRootPairParameters.count s := hblock
    _ = 2 * ((realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2) := by
      rw [hparams]
    _ = (realPolynomialToComplex A).rootMultiplicity (s : ℂ) := by
      exact two_mul_half_of_even
        (hA.rootProductData.facts.complex_ofReal_interior_multiplicity_even
          ⟨by linarith [hscond.1], hscond.2⟩)
    _ = data.roots.count (s : ℂ) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (s : ℂ)).symm

/-- For the negative partner of a selected interior real root, the grouped
source block has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.interiorGroupedBlock_count_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveInteriorRealRootValues) :
    (hA.rootProductData.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
      [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (-(s : ℂ)) =
      hA.rootProductData.roots.count (-(s : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hscond : 0 < s ∧ s < 1 :=
    SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := data) hs
  have hparams_pos :
      ∀ t ∈ data.interiorRealRootPairParameters, 0 < t := by
    intro t ht
    exact (SourceRootProductData.mem_interiorRealRootPairParameters
      (data := data) ht).1.1
  have hblock :=
    list_count_flatMap_real_four_orbit_neg
      data.interiorRealRootPairParameters s hparams_pos hscond.1
  have hparams :=
    SourceRootProductData.count_interiorRealRootPairParameters
      (A := A) (data := data) hs
  calc
    (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
      [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (-(s : ℂ)) =
        2 * data.interiorRealRootPairParameters.count s := hblock
    _ = 2 * ((realPolynomialToComplex A).rootMultiplicity (s : ℂ) / 2) := by
      rw [hparams]
    _ = (realPolynomialToComplex A).rootMultiplicity (s : ℂ) := by
      exact two_mul_half_of_even
        (hA.rootProductData.facts.complex_ofReal_interior_multiplicity_even
          ⟨by linarith [hscond.1], hscond.2⟩)
    _ = (realPolynomialToComplex A).rootMultiplicity (-(s : ℂ)) := by
      exact (hA.rootProductData.facts.complex_neg_multiplicity (s : ℂ)).symm
    _ = data.roots.count (-(s : ℂ)) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (-(s : ℂ))).symm

/-- For a selected positive interior real root, the whole grouped source root
list has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_interior_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveInteriorRealRootValues) :
    (hA.rootProductData).groupedRootList.count (s : ℂ) =
      (hA.rootProductData).roots.count (s : ℂ) := by
  classical
  let data := hA.rootProductData
  have hscond : 0 < s ∧ s < 1 :=
    SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := data) hs
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have hs0 : s = 0 := by
      apply Complex.ofReal_injective
      simpa using List.eq_of_mem_replicate hw
    linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    · have ht : t.value = s := Complex.ofReal_injective (by simpa using hmem.symm)
      nlinarith [t.outside, hscond.1, hscond.2]
    · have ht : t.value = -s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      nlinarith [t.outside, hscond.1, hscond.2]
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have hinterior := hA.interiorGroupedBlock_count_positive (s := s) hs
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- For the negative partner of a selected interior real root, the whole
grouped source root list has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:445,452-454,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_interior_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveInteriorRealRootValues) :
    (hA.rootProductData).groupedRootList.count (-(s : ℂ)) =
      (hA.rootProductData).roots.count (-(s : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hscond : 0 < s ∧ s < 1 :=
    SourceRootProductData.mem_positiveInteriorRealRootValues
      (data := data) hs
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have hs0 : s = 0 := by
      apply Complex.ofReal_injective
      simpa using congrArg Neg.neg (List.eq_of_mem_replicate hw)
    linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    · have ht : t.value = -s := by
        apply Complex.ofReal_injective
        simpa using hmem.symm
      nlinarith [t.outside, hscond.1, hscond.2]
    · have ht : t.value = s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      nlinarith [t.outside, hscond.1, hscond.2]
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have hinterior := hA.interiorGroupedBlock_count_negative (s := s) hs
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- The grouped outside-real block has the same cardinality as the canonical
outside-real root class [GSLW19, BlockHam.tex:446,453-460,469-479]. -/
theorem SourceHypotheses.outsideGroupedBlock_length_eq_countP_outside
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData.outsideRealRoots.flatMap (fun s : OutsideRealRoot =>
      [(s.value : ℂ), -(s.value : ℂ)])).length =
      @Multiset.countP ℂ IsOutsideRealRootClass
        (fun z => Classical.propDecidable (IsOutsideRealRootClass z))
        (hA.rootProductData).roots := by
  classical
  let data := hA.rootProductData
  have hlen :
      (data.outsideRealRoots.flatMap (fun s : OutsideRealRoot =>
        [(s.value : ℂ), -(s.value : ℂ)])).length =
        2 * data.outsideRealRoots.length := by
    simp [List.length_flatMap, Nat.mul_comm]
  have hparams :
      data.outsideRealRoots.length =
        (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum := by
    rw [SourceRootProductData.length_outsideRealRoots,
      SourceRootProductData.length_outsideRealRootParameters]
  have hpositive :
      (data.positiveOutsideRealRootValues.map fun s : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).sum =
        @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) data.roots := by
    simpa [data] using hA.sum_rootMultiplicity_positiveOutside_eq_countP
  have hclass :
      @Multiset.countP ℂ IsOutsideRealRootClass
        (fun z => Classical.propDecidable (IsOutsideRealRootClass z))
        data.roots =
        2 * @Multiset.countP ℂ IsPositiveOutsideRealRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveOutsideRealRootRepresentative z)) data.roots := by
    simpa [data] using hA.countP_outsideRealRootClass_eq_two_mul_countP_positiveOutside
  rw [hlen, hparams, hclass, hpositive]

/-- For a selected positive outside-real root, the grouped source block has
exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:446,453-460,469-479]. -/
theorem SourceHypotheses.outsideGroupedBlock_count_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveOutsideRealRootValues) :
    (hA.rootProductData.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
      [(t.value : ℂ), -(t.value : ℂ)])).count (s : ℂ) =
      hA.rootProductData.roots.count (s : ℂ) := by
  classical
  let data := hA.rootProductData
  have hspos : 0 < s := by
    have hsone : 1 ≤ s :=
      SourceRootProductData.mem_positiveOutsideRealRootValues
        (data := data) hs
    linarith
  have hparams_pos :
      ∀ t ∈ data.outsideRealRoots, 0 < t.value := by
    intro t ht
    exact SourceRootProductData.value_pos_of_mem_outsideRealRoots
      (data := data) ht
  have hblock :=
    list_count_flatMap_key_real_two_orbit
      data.outsideRealRoots (fun t : OutsideRealRoot => t.value) s
      hparams_pos hspos
  have hvalues := SourceRootProductData.map_value_outsideRealRoots data
  have hparams :=
    SourceRootProductData.count_outsideRealRootParameters
      (A := A) (data := data) hs
  calc
    (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
      [(t.value : ℂ), -(t.value : ℂ)])).count (s : ℂ) =
        (data.outsideRealRoots.map fun t : OutsideRealRoot => t.value).count s := hblock
    _ = data.outsideRealRootParameters.count s := by
      rw [hvalues]
    _ = (realPolynomialToComplex A).rootMultiplicity (s : ℂ) := by
      rw [hparams]
    _ = data.roots.count (s : ℂ) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (s : ℂ)).symm

/-- For the negative partner of a selected outside-real root, the grouped
source block has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:446,453-460,469-479]. -/
theorem SourceHypotheses.outsideGroupedBlock_count_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveOutsideRealRootValues) :
    (hA.rootProductData.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
      [(t.value : ℂ), -(t.value : ℂ)])).count (-(s : ℂ)) =
      hA.rootProductData.roots.count (-(s : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hspos : 0 < s := by
    have hsone : 1 ≤ s :=
      SourceRootProductData.mem_positiveOutsideRealRootValues
        (data := data) hs
    linarith
  have hparams_pos :
      ∀ t ∈ data.outsideRealRoots, 0 < t.value := by
    intro t ht
    exact SourceRootProductData.value_pos_of_mem_outsideRealRoots
      (data := data) ht
  have hblock :=
    list_count_flatMap_key_real_two_orbit_neg
      data.outsideRealRoots (fun t : OutsideRealRoot => t.value) s
      hparams_pos hspos
  have hvalues := SourceRootProductData.map_value_outsideRealRoots data
  have hparams :=
    SourceRootProductData.count_outsideRealRootParameters
      (A := A) (data := data) hs
  calc
    (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
      [(t.value : ℂ), -(t.value : ℂ)])).count (-(s : ℂ)) =
        (data.outsideRealRoots.map fun t : OutsideRealRoot => t.value).count s := hblock
    _ = data.outsideRealRootParameters.count s := by
      rw [hvalues]
    _ = (realPolynomialToComplex A).rootMultiplicity (s : ℂ) := by
      rw [hparams]
    _ = (realPolynomialToComplex A).rootMultiplicity (-(s : ℂ)) := by
      exact (hA.rootProductData.facts.complex_neg_multiplicity (s : ℂ)).symm
    _ = data.roots.count (-(s : ℂ)) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (-(s : ℂ))).symm

/-- For a selected positive outside/end-point real root, the whole grouped
source root list has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:446,453-460,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_outside_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveOutsideRealRootValues) :
    (hA.rootProductData).groupedRootList.count (s : ℂ) =
      (hA.rootProductData).roots.count (s : ℂ) := by
  classical
  let data := hA.rootProductData
  have hsone : 1 ≤ s :=
    SourceRootProductData.mem_positiveOutsideRealRootValues
      (data := data) hs
  have hspos : 0 < s := by linarith
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have hs0 : s = 0 := by
      apply Complex.ofReal_injective
      simpa using List.eq_of_mem_replicate hw
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, ht, hmem⟩
    have htcond := SourceRootProductData.mem_interiorRealRootPairParameters
      (data := data) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    · have hts : t = s := Complex.ofReal_injective (by simpa using hmem.symm)
      linarith [htcond.1.2, hsone]
    · have hts : t = -s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      linarith [htcond.1.1, hsone]
    · have hts : t = s := Complex.ofReal_injective (by simpa using hmem.symm)
      linarith [htcond.1.2, hsone]
    · have hts : t = -s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      linarith [htcond.1.1, hsone]
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (s : ℂ) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have houtside := hA.outsideGroupedBlock_count_positive (s := s) hs
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- For the negative partner of a selected outside/end-point real root, the
whole grouped source root list has exactly the canonical root multiplicity
[GSLW19, BlockHam.tex:446,453-460,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_outside_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {s : ℝ}
    (hs : s ∈ hA.rootProductData.positiveOutsideRealRootValues) :
    (hA.rootProductData).groupedRootList.count (-(s : ℂ)) =
      (hA.rootProductData).roots.count (-(s : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hsone : 1 ≤ s :=
    SourceRootProductData.mem_positiveOutsideRealRootValues
      (data := data) hs
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have hs0 : s = 0 := by
      apply Complex.ofReal_injective
      simpa using congrArg Neg.neg (List.eq_of_mem_replicate hw)
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, ht, hmem⟩
    have htcond := SourceRootProductData.mem_interiorRealRootPairParameters
      (data := data) ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    · have hts : t = -s := by
        apply Complex.ofReal_injective
        simpa using hmem.symm
      linarith [htcond.1.1, hsone]
    · have hts : t = s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      linarith [htcond.1.2, hsone]
    · have hts : t = -s := by
        apply Complex.ofReal_injective
        simpa using hmem.symm
      linarith [htcond.1.1, hsone]
    · have hts : t = s := by
        apply Complex.ofReal_injective
        simpa using (congrArg Neg.neg hmem).symm
      linarith [htcond.1.2, hsone]
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (-(s : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have houtside := hA.outsideGroupedBlock_count_negative (s := s) hs
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- The grouped pure-imaginary block has the same cardinality as the canonical
pure-imaginary root class [GSLW19, BlockHam.tex:447,455,461,469-479]. -/
theorem SourceHypotheses.imaginaryGroupedBlock_length_eq_countP_imaginary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData.imaginaryRootParameters.flatMap (fun r : ℝ =>
      [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).length =
      @Multiset.countP ℂ IsImaginaryRootClass
        (fun z => Classical.propDecidable (IsImaginaryRootClass z))
        (hA.rootProductData).roots := by
  classical
  let data := hA.rootProductData
  have hlen :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).length =
        2 * data.imaginaryRootParameters.length := by
    simp [List.length_flatMap, Nat.mul_comm]
  have hparams :
      data.imaginaryRootParameters.length =
        (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum := by
    simpa [data] using
      SourceRootProductData.length_imaginaryRootParameters
        (A := A) hA.rootProductData
  have hpositive :
      (data.positiveImaginaryRootValues.map fun r : ℝ =>
          (realPolynomialToComplex A).rootMultiplicity (Complex.I * (r : ℂ))).sum =
        @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) data.roots := by
    simpa [data] using hA.sum_rootMultiplicity_positiveImaginary_eq_countP
  have hclass :
      @Multiset.countP ℂ IsImaginaryRootClass
        (fun z => Classical.propDecidable (IsImaginaryRootClass z))
        data.roots =
        2 * @Multiset.countP ℂ IsPositiveImaginaryRootRepresentative
          (fun z => Classical.propDecidable
            (IsPositiveImaginaryRootRepresentative z)) data.roots := by
    simpa [data] using hA.countP_imaginaryRootClass_eq_two_mul_countP_positiveImaginary
  rw [hlen, hparams, hclass, hpositive]

/-- For a selected positive imaginary root, the grouped source block has
exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:447,455,461,469-479]. -/
theorem SourceHypotheses.imaginaryGroupedBlock_count_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ hA.rootProductData.positiveImaginaryRootValues) :
    (hA.rootProductData.imaginaryRootParameters.flatMap (fun t : ℝ =>
      [Complex.I * (t : ℂ), -(Complex.I * (t : ℂ))])).count
        (Complex.I * (r : ℂ)) =
      hA.rootProductData.roots.count (Complex.I * (r : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hrpos : 0 < r :=
    SourceRootProductData.mem_positiveImaginaryRootValues
      (data := data) hr
  have hparams_pos :
      ∀ t ∈ data.imaginaryRootParameters, 0 < t := by
    intro t ht
    exact (SourceRootProductData.mem_imaginaryRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_imaginary_two_orbit
      data.imaginaryRootParameters r hparams_pos hrpos
  have hparams :=
    SourceRootProductData.count_imaginaryRootParameters
      (A := A) (data := data) hr
  calc
    (data.imaginaryRootParameters.flatMap (fun t : ℝ =>
      [Complex.I * (t : ℂ), -(Complex.I * (t : ℂ))])).count
        (Complex.I * (r : ℂ)) =
        data.imaginaryRootParameters.count r := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity
        (Complex.I * (r : ℂ)) := by
      rw [hparams]
    _ = data.roots.count (Complex.I * (r : ℂ)) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity
        (Complex.I * (r : ℂ))).symm

/-- For the negative partner of a selected positive imaginary root, the
grouped source block has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:447,455,461,469-479]. -/
theorem SourceHypotheses.imaginaryGroupedBlock_count_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ hA.rootProductData.positiveImaginaryRootValues) :
    (hA.rootProductData.imaginaryRootParameters.flatMap (fun t : ℝ =>
      [Complex.I * (t : ℂ), -(Complex.I * (t : ℂ))])).count
        (-(Complex.I * (r : ℂ))) =
      hA.rootProductData.roots.count (-(Complex.I * (r : ℂ))) := by
  classical
  let data := hA.rootProductData
  have hrpos : 0 < r :=
    SourceRootProductData.mem_positiveImaginaryRootValues
      (data := data) hr
  have hparams_pos :
      ∀ t ∈ data.imaginaryRootParameters, 0 < t := by
    intro t ht
    exact (SourceRootProductData.mem_imaginaryRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_imaginary_two_orbit_neg
      data.imaginaryRootParameters r hparams_pos hrpos
  have hparams :=
    SourceRootProductData.count_imaginaryRootParameters
      (A := A) (data := data) hr
  calc
    (data.imaginaryRootParameters.flatMap (fun t : ℝ =>
      [Complex.I * (t : ℂ), -(Complex.I * (t : ℂ))])).count
        (-(Complex.I * (r : ℂ))) =
        data.imaginaryRootParameters.count r := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity
        (Complex.I * (r : ℂ)) := by
      rw [hparams]
    _ = (realPolynomialToComplex A).rootMultiplicity
        (-(Complex.I * (r : ℂ))) := by
      exact (hA.rootProductData.facts.complex_neg_multiplicity
        (Complex.I * (r : ℂ))).symm
    _ = data.roots.count (-(Complex.I * (r : ℂ))) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity
        (-(Complex.I * (r : ℂ)))).symm

/-- For a selected positive imaginary root, the whole grouped source root list
has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:447,455,461,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_imaginary_positive
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ hA.rootProductData.positiveImaginaryRootValues) :
    (hA.rootProductData).groupedRootList.count (Complex.I * (r : ℂ)) =
      (hA.rootProductData).roots.count (Complex.I * (r : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hrpos : 0 < r :=
    SourceRootProductData.mem_positiveImaginaryRootValues
      (data := data) hr
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count
        (Complex.I * (r : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have him := congrArg Complex.im (List.eq_of_mem_replicate hw)
    simp at him
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count
          (Complex.I * (r : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count (Complex.I * (r : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (Complex.I * (r : ℂ)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have himag := hA.imaginaryGroupedBlock_count_positive (r := r) hr
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- For the negative partner of a selected positive imaginary root, the whole
grouped source root list has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:447,455,461,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_imaginary_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {r : ℝ}
    (hr : r ∈ hA.rootProductData.positiveImaginaryRootValues) :
    (hA.rootProductData).groupedRootList.count (-(Complex.I * (r : ℂ))) =
      (hA.rootProductData).roots.count (-(Complex.I * (r : ℂ))) := by
  classical
  let data := hA.rootProductData
  have hrpos : 0 < r :=
    SourceRootProductData.mem_positiveImaginaryRootValues
      (data := data) hr
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count
        (-(Complex.I * (r : ℂ))) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have him := congrArg Complex.im (List.eq_of_mem_replicate hw)
    simp at him
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count
          (-(Complex.I * (r : ℂ))) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count
          (-(Complex.I * (r : ℂ))) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp at him
      linarith
  have hcomplex :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).count
          (-(Complex.I * (r : ℂ))) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨z, hz, hmem⟩
    have hzpos := (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp at hre
      linarith
  have himag := hA.imaginaryGroupedBlock_count_negative (r := r) hr
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag, hcomplex]
  simp

/-- The grouped non-real quartet block has the same cardinality as the canonical
complex-quartet root class [GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.complexGroupedBlock_length_eq_countP_complex
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    (hA.rootProductData.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
      complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).length =
      @Multiset.countP ℂ IsComplexQuartetRootClass
        (fun z => Classical.propDecidable (IsComplexQuartetRootClass z))
        (hA.rootProductData).roots := by
  classical
  let data := hA.rootProductData
  have hlen :
      (data.complexRootParameters.flatMap (fun z : ℝ × ℝ =>
        complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))).length =
        4 * data.complexRootParameters.length := by
    simp [List.length_flatMap, complexRootOrbit, Nat.mul_comm]
  have hparams :
      data.complexRootParameters.length =
        (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (realPolynomialToComplex A).rootMultiplicity z).sum := by
    simpa [data] using
      SourceRootProductData.length_complexRootParameters
        (A := A) hA.rootProductData
  have hpositive :
      (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
          (realPolynomialToComplex A).rootMultiplicity z).sum =
        @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
    simpa [data] using hA.sum_rootMultiplicity_firstQuadrant_eq_countP
  have hclass :
      @Multiset.countP ℂ IsComplexQuartetRootClass
        (fun z => Classical.propDecidable (IsComplexQuartetRootClass z))
        data.roots =
        4 * @Multiset.countP ℂ IsFirstQuadrantComplexRootRepresentative
          (fun z => Classical.propDecidable
            (IsFirstQuadrantComplexRootRepresentative z)) data.roots := by
    simpa [data] using hA.countP_complexQuartetRootClass_eq_four_mul_countP_firstQuadrant
  rw [hlen, hparams, hclass, hpositive]

/-- For a selected first-quadrant non-real root, the grouped source block has
exactly the canonical root multiplicity at the representative root [GSLW19,
BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.complexGroupedBlock_count_primary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) =
      hA.rootProductData.roots.count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := by
  classical
  let data := hA.rootProductData
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hparams_pos :
      ∀ t ∈ data.complexRootParameters, 0 < t.1 ∧ 0 < t.2 := by
    intro t ht
    exact (SourceRootProductData.mem_complexRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_complex_orbit
      data.complexRootParameters z.1 z.2 hparams_pos hzpos.1 hzpos.2
  have hparams :=
    SourceRootProductData.count_complexRootParameters_of_mem
      (A := A) (data := data) hz
  calc
    (data.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) =
        data.complexRootParameters.count z := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := hparams
    _ = data.roots.count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).symm

/-- For the negative partner of a selected first-quadrant non-real root, the
grouped source block has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.complexGroupedBlock_count_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (-((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
      hA.rootProductData.roots.count
        (-((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hparams_pos :
      ∀ t ∈ data.complexRootParameters, 0 < t.1 ∧ 0 < t.2 := by
    intro t ht
    exact (SourceRootProductData.mem_complexRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_complex_orbit_neg
      data.complexRootParameters z.1 z.2 hparams_pos hzpos.1 hzpos.2
  have hparams :=
    SourceRootProductData.count_complexRootParameters_of_mem
      (A := A) (data := data) hz
  calc
    (data.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (-((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
        data.complexRootParameters.count z := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity w := by
      simpa [w] using hparams
    _ = (realPolynomialToComplex A).rootMultiplicity (-w) := by
      exact (hA.rootProductData.facts.complex_neg_multiplicity w).symm
    _ = data.roots.count (-w) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity (-w)).symm

/-- For the conjugate partner of a selected first-quadrant non-real root, the
grouped source block has exactly the canonical root multiplicity [GSLW19,
BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.complexGroupedBlock_count_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
      hA.rootProductData.roots.count
        (starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hparams_pos :
      ∀ t ∈ data.complexRootParameters, 0 < t.1 ∧ 0 < t.2 := by
    intro t ht
    exact (SourceRootProductData.mem_complexRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_complex_orbit_conj
      data.complexRootParameters z.1 z.2 hparams_pos hzpos.1 hzpos.2
  have hparams :=
    SourceRootProductData.count_complexRootParameters_of_mem
      (A := A) (data := data) hz
  calc
    (data.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
        data.complexRootParameters.count z := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity w := by
      simpa [w] using hparams
    _ = (realPolynomialToComplex A).rootMultiplicity (starRingEnd ℂ w) := by
      exact (hA.rootProductData.facts.complex_conj_multiplicity w).symm
    _ = data.roots.count (starRingEnd ℂ w) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity
        (starRingEnd ℂ w)).symm

/-- For the negative conjugate partner of a selected first-quadrant non-real
root, the grouped source block has exactly the canonical root multiplicity
[GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.complexGroupedBlock_count_neg_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (-(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))) =
      hA.rootProductData.roots.count
        (-(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hparams_pos :
      ∀ t ∈ data.complexRootParameters, 0 < t.1 ∧ 0 < t.2 := by
    intro t ht
    exact (SourceRootProductData.mem_complexRootParameters
      (data := data) ht).1
  have hblock :=
    list_count_flatMap_complex_orbit_neg_conj
      data.complexRootParameters z.1 z.2 hparams_pos hzpos.1 hzpos.2
  have hparams :=
    SourceRootProductData.count_complexRootParameters_of_mem
      (A := A) (data := data) hz
  calc
    (data.complexRootParameters.flatMap (fun t : ℝ × ℝ =>
      complexRootOrbit ((t.1 : ℂ) + Complex.I * (t.2 : ℂ)))).count
        (-(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))) =
        data.complexRootParameters.count z := hblock
    _ = (realPolynomialToComplex A).rootMultiplicity w := by
      simpa [w] using hparams
    _ = (realPolynomialToComplex A).rootMultiplicity (-(starRingEnd ℂ w)) := by
      calc
        (realPolynomialToComplex A).rootMultiplicity w =
            (realPolynomialToComplex A).rootMultiplicity (starRingEnd ℂ w) := by
          exact (hA.rootProductData.facts.complex_conj_multiplicity w).symm
        _ = (realPolynomialToComplex A).rootMultiplicity (-(starRingEnd ℂ w)) := by
          exact (hA.rootProductData.facts.complex_neg_multiplicity
            (starRingEnd ℂ w)).symm
    _ = data.roots.count (-(starRingEnd ℂ w)) := by
      exact (hA.rootProductData_count_eq_rootMultiplicity
        (-(starRingEnd ℂ w))).symm

/-- For a selected first-quadrant non-real root, the whole grouped source root
list has exactly the canonical root multiplicity at the representative root
[GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_complex_primary
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData).groupedRootList.count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) =
      (hA.rootProductData).roots.count
        ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count w = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have h0 : w = 0 := List.eq_of_mem_replicate hw
    have him := congrArg Complex.im h0
    simp [w] at him
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count w = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w] at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count w = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w] at him
      linarith
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count w = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp [w] at hre
      linarith
  have hcomplex :=
    hA.complexGroupedBlock_count_primary (z := z) hz
  simp [SourceRootProductData.groupedRootList, data, w, List.count_append,
    hzero, hinterior, houtside, himag, hcomplex]

/-- For the negative partner of a selected first-quadrant non-real root, the
whole grouped source root list has exactly the canonical root multiplicity
[GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_complex_negative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData).groupedRootList.count
        (-((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
      (hA.rootProductData).roots.count
        (-((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count (-w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have h0 : -w = 0 := List.eq_of_mem_replicate hw
    have him := congrArg Complex.im h0
    simp [w] at him
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count (-w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w] at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count (-w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w] at him
      linarith
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count (-w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp [w] at hre
      linarith
  have hcomplex :=
    hA.complexGroupedBlock_count_negative (z := z) hz
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag]
  simpa [data, w, add_assoc, add_comm, add_left_comm] using hcomplex

/-- For the conjugate partner of a selected first-quadrant non-real root, the
whole grouped source root list has exactly the canonical root multiplicity
[GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_complex_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData).groupedRootList.count
        (starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) =
      (hA.rootProductData).roots.count
        (starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count
        (starRingEnd ℂ w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have h0 : starRingEnd ℂ w = 0 := List.eq_of_mem_replicate hw
    have him := congrArg Complex.im h0
    simp [w, Complex.conj_I, Complex.conj_ofReal] at him
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count
          (starRingEnd ℂ w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count (starRingEnd ℂ w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at him
      linarith
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count
          (starRingEnd ℂ w) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at hre
      linarith
  have hcomplex :=
    hA.complexGroupedBlock_count_conj (z := z) hz
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag]
  simpa [data, w, Complex.conj_I, Complex.conj_ofReal, add_assoc, add_comm,
    add_left_comm] using hcomplex

/-- For the negative conjugate partner of a selected first-quadrant non-real
root, the whole grouped source root list has exactly the canonical root
multiplicity [GSLW19, BlockHam.tex:448,455-456,462-466,469-479]. -/
theorem SourceHypotheses.groupedRootList_count_complex_neg_conj
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℝ × ℝ}
    (hz : z ∈ hA.rootProductData.complexRootParameters) :
    (hA.rootProductData).groupedRootList.count
        (-(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))) =
      (hA.rootProductData).roots.count
        (-(starRingEnd ℂ ((z.1 : ℂ) + Complex.I * (z.2 : ℂ)))) := by
  classical
  let data := hA.rootProductData
  let w : ℂ := (z.1 : ℂ) + Complex.I * (z.2 : ℂ)
  have hzpos : 0 < z.1 ∧ 0 < z.2 :=
    (SourceRootProductData.mem_complexRootParameters
      (data := data) hz).1
  have hzero :
      (List.replicate (2 * data.zeroRootPairs) (0 : ℂ)).count
        (-(starRingEnd ℂ w)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    have h0 : -(starRingEnd ℂ w) = 0 := List.eq_of_mem_replicate hw
    have hre := congrArg Complex.re h0
    simp [w, Complex.conj_I, Complex.conj_ofReal] at hre
    linarith
  have hinterior :
      (data.interiorRealRootPairParameters.flatMap (fun t : ℝ =>
        [(t : ℂ), -(t : ℂ), (t : ℂ), -(t : ℂ)])).count
          (-(starRingEnd ℂ w)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem | hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at him
      linarith
  have houtside :
      (data.outsideRealRoots.flatMap (fun t : OutsideRealRoot =>
        [(t.value : ℂ), -(t.value : ℂ)])).count
          (-(starRingEnd ℂ w)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨t, _ht, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have him := congrArg Complex.im hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at him
      linarith
  have himag :
      (data.imaginaryRootParameters.flatMap (fun r : ℝ =>
        [Complex.I * (r : ℂ), -(Complex.I * (r : ℂ))])).count
          (-(starRingEnd ℂ w)) = 0 := by
    rw [List.count_eq_zero]
    intro hw
    rcases List.mem_flatMap.mp hw with ⟨r, _hr, hmem⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with hmem | hmem
    all_goals
      have hre := congrArg Complex.re hmem
      simp [w, Complex.conj_I, Complex.conj_ofReal] at hre
      linarith
  have hcomplex :=
    hA.complexGroupedBlock_count_neg_conj (z := z) hz
  rw [SourceRootProductData.groupedRootList]
  simp only [List.count_append]
  rw [hzero, hinterior, houtside, himag]
  simpa [data, w, Complex.conj_I, Complex.conj_ofReal, add_assoc, add_comm,
    add_left_comm] using hcomplex

/-- The zero-root block of the grouped source list uses no more multiplicity
than the canonical root multiset [GSLW19, BlockHam.tex:442-452]. -/
theorem SourceHypotheses.zeroRootGroupedList_le_roots
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((List.replicate (2 * (hA.rootProductData).zeroRootPairs) (0 : ℂ)) :
      Multiset ℂ) ≤ (hA.rootProductData).roots := by
  classical
  rw [Multiset.le_iff_count]
  intro z
  by_cases hz : z = 0
  · subst z
    simp only [Multiset.coe_count, List.count_replicate_self]
    rw [(hA.rootProductData).two_mul_zeroRootPairs,
      hA.rootProductData_count_eq_rootMultiplicity]
  · simp [hz]

/-- Every entry of the grouped source root list is a canonical complex root.
This is the element-level half of the source root-class partition
[GSLW19, BlockHam.tex:450-456]. -/
theorem SourceHypotheses.mem_roots_of_mem_groupedRootList
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) {z : ℂ}
    (hz : z ∈ (hA.rootProductData).groupedRootList) :
    z ∈ (hA.rootProductData).roots := by
  classical
  simp only [SourceRootProductData.groupedRootList, List.mem_append,
    List.mem_replicate, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, Prod.exists] at hz
  rcases hz with (((hzero | hint) | houtside) | himag) | hcomplex
  · rcases hzero with ⟨hlen, rfl⟩
    apply Multiset.count_pos.mp
    have hpos : 0 < 2 * (hA.rootProductData).zeroRootPairs :=
      Nat.pos_of_ne_zero hlen
    calc
      0 < 2 * (hA.rootProductData).zeroRootPairs := hpos
      _ = (hA.rootProductData).roots.count (0 : ℂ) := by
        rw [(hA.rootProductData).two_mul_zeroRootPairs,
          hA.rootProductData_count_eq_rootMultiplicity]
  · rcases hint with ⟨s, hs, hzmem⟩
    rcases hzmem with rfl | rfl | rfl | rfl
    · exact (SourceRootProductData.mem_interiorRealRootPairParameters
        (data := hA.rootProductData) hs).2
    · exact hA.neg_mem_rootProductData_of_mem_interiorRealRootPairParameters hs
    · exact (SourceRootProductData.mem_interiorRealRootPairParameters
        (data := hA.rootProductData) hs).2
    · exact hA.neg_mem_rootProductData_of_mem_interiorRealRootPairParameters hs
  · rcases houtside with ⟨s, hs, hzmem⟩
    have hsroot :
        (s.value : ℂ) ∈ (hA.rootProductData).roots :=
      SourceRootProductData.root_mem_of_mem_outsideRealRoots
        (data := hA.rootProductData) hs
    rcases hzmem with rfl | rfl
    · exact hsroot
    · exact hA.mem_rootProductData_roots_of_mem_complexRootOrbit hsroot
        (by simp [complexRootOrbit])
  · rcases himag with ⟨r, hr, hzmem⟩
    rcases hzmem with rfl | rfl
    · exact (SourceRootProductData.mem_imaginaryRootParameters
        (data := hA.rootProductData) hr).2
    · exact hA.neg_imag_mem_rootProductData_of_mem_imaginaryRootParameters hr
  · rcases hcomplex with ⟨a, b, hz0, hzmem⟩
    let z0 : ℝ × ℝ := (a, b)
    let w : ℂ := (z0.1 : ℂ) + Complex.I * (z0.2 : ℂ)
    have hw : w ∈ (hA.rootProductData).roots :=
      (SourceRootProductData.mem_complexRootParameters
        (data := hA.rootProductData) hz0).2
    have hcompanions :
        -w ∈ (hA.rootProductData).roots ∧
          starRingEnd ℂ w ∈ (hA.rootProductData).roots ∧
            -(starRingEnd ℂ w) ∈ (hA.rootProductData).roots := by
      simpa [w, z0] using
        hA.complex_quartet_mem_rootProductData_of_mem_complexRootParameters hz0
    simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil, or_false] at hzmem
    rcases hzmem with rfl | rfl | rfl | rfl
    · exact hw
    · simpa [w, z0] using hcompanions.1
    · simpa [w, z0] using hcompanions.2.1
    · simpa [w, z0] using hcompanions.2.2

/-- The grouped source root list has exactly the canonical root multiplicity
at every complex number.  This is the count-ext form of the source root-class
partition before turning the grouped product into the displayed product
[GSLW19, BlockHam.tex:450-480]. -/
theorem SourceHypotheses.groupedRootList_count_eq_roots
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) (z : ℂ) :
    (hA.rootProductData).groupedRootList.count z =
      (hA.rootProductData).roots.count z := by
  classical
  let data := hA.rootProductData
  by_cases hzroot : z ∈ data.roots
  · rcases hA.exists_sourceRepresentative_mem_rootProductData
      (by simpa [data] using hzroot) with
      ⟨w, hwroot, hworbit, hwrep⟩
    have hzw : z ∈ complexRootOrbit w := mem_complexRootOrbit_symm hworbit
    rcases hwrep with hzero | hinterior | houtside | himag | hcomplex
    · subst w
      simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hzw
      rcases hzw with h | h | h | h
      · subst z
        simpa [data] using hA.groupedRootList_count_zero
      · subst z
        simpa [data] using hA.groupedRootList_count_zero
      · subst z
        simpa [data] using hA.groupedRootList_count_zero
      · rcases h with h | hfalse
        · subst z
          simpa [data] using hA.groupedRootList_count_zero
        · cases hfalse
    · have hs : w.re ∈ data.positiveInteriorRealRootValues :=
        SourceRootProductData.mem_positiveInteriorRealRootValues_of_root_mem
          (data := data) (by simpa [data] using hwroot) hinterior
      have hwreal : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using hinterior.1
      have hzorbit : z ∈ complexRootOrbit (w.re : ℂ) := by
        rw [hwreal] at hzw
        exact hzw
      simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hzorbit
      rcases hzorbit with h | h | h | h
      · subst z
        simpa [data] using
          hA.groupedRootList_count_interior_positive (s := w.re) hs
      · subst z
        simpa [data] using
          hA.groupedRootList_count_interior_negative (s := w.re) hs
      · subst z
        simpa [data, Complex.conj_ofReal] using
          hA.groupedRootList_count_interior_positive (s := w.re) hs
      · rcases h with h | hfalse
        · subst z
          simpa [data, Complex.conj_ofReal] using
            hA.groupedRootList_count_interior_negative (s := w.re) hs
        · cases hfalse
    · have hs : w.re ∈ data.positiveOutsideRealRootValues :=
        SourceRootProductData.mem_positiveOutsideRealRootValues_of_root_mem
          (data := data) (by simpa [data] using hwroot) houtside
      have hwreal : w = (w.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa using houtside.1
      have hzorbit : z ∈ complexRootOrbit (w.re : ℂ) := by
        rw [hwreal] at hzw
        exact hzw
      simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hzorbit
      rcases hzorbit with h | h | h | h
      · subst z
        simpa [data] using
          hA.groupedRootList_count_outside_positive (s := w.re) hs
      · subst z
        simpa [data] using
          hA.groupedRootList_count_outside_negative (s := w.re) hs
      · subst z
        simpa [data, Complex.conj_ofReal] using
          hA.groupedRootList_count_outside_positive (s := w.re) hs
      · rcases h with h | hfalse
        · subst z
          simpa [data, Complex.conj_ofReal] using
            hA.groupedRootList_count_outside_negative (s := w.re) hs
        · cases hfalse
    · have hr : w.im ∈ data.positiveImaginaryRootValues :=
        SourceRootProductData.mem_positiveImaginaryRootValues_of_root_mem
          (data := data) (by simpa [data] using hwroot) himag
      have hwimag : w = Complex.I * (w.im : ℂ) := by
        apply Complex.ext
        · simpa using himag.1
        · simp
      have hzorbit : z ∈ complexRootOrbit (Complex.I * (w.im : ℂ)) := by
        rw [hwimag] at hzw
        exact hzw
      simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hzorbit
      rcases hzorbit with h | h | h | h
      · subst z
        simpa [data] using
          hA.groupedRootList_count_imaginary_positive (r := w.im) hr
      · subst z
        simpa [data] using
          hA.groupedRootList_count_imaginary_negative (r := w.im) hr
      · subst z
        simpa [data, Complex.conj_I, Complex.conj_ofReal] using
          hA.groupedRootList_count_imaginary_negative (r := w.im) hr
      · rcases h with h | hfalse
        · subst z
          simpa [data, Complex.conj_I, Complex.conj_ofReal] using
            hA.groupedRootList_count_imaginary_positive (r := w.im) hr
        · cases hfalse
    · have hwrepList :
          w ∈ data.firstQuadrantComplexRootRepresentatives := by
        rw [SourceRootProductData.firstQuadrantComplexRootRepresentatives]
        exact List.mem_filter.mpr
          ⟨List.mem_dedup.mpr (Multiset.mem_toList.mpr (by simpa [data] using hwroot)),
            show decide (IsFirstQuadrantComplexRootRepresentative w) = true from
              decide_eq_true hcomplex⟩
      have hzparam : (w.re, w.im) ∈ data.complexRootParameters := by
        rw [SourceRootProductData.complexRootParameters]
        refine List.mem_flatMap.mpr ⟨w, hwrepList, ?_⟩
        rw [List.mem_replicate]
        constructor
        · have hpos :
              0 < (realPolynomialToComplex A).rootMultiplicity w := by
            rw [← hA.rootProductData_count_eq_rootMultiplicity w]
            exact Multiset.count_pos.mpr (by simpa [data] using hwroot)
          exact Nat.ne_of_gt hpos
        · rfl
      have hwcart : ((w.re : ℂ) + Complex.I * (w.im : ℂ)) = w := by
        apply Complex.ext <;> simp
      simp only [complexRootOrbit, List.mem_cons, List.not_mem_nil] at hzw
      rcases hzw with h | h | h | h
      · subst z
        simpa [data, hwcart] using
          hA.groupedRootList_count_complex_primary (z := (w.re, w.im)) hzparam
      · subst z
        simpa [data, hwcart] using
          hA.groupedRootList_count_complex_negative (z := (w.re, w.im)) hzparam
      · subst z
        simpa [data, hwcart] using
          hA.groupedRootList_count_complex_conj (z := (w.re, w.im)) hzparam
      · rcases h with h | hfalse
        · subst z
          simpa [data, hwcart] using
            hA.groupedRootList_count_complex_neg_conj (z := (w.re, w.im)) hzparam
        · cases hfalse
  · have hgroup :
        data.groupedRootList.count z = 0 := by
      rw [List.count_eq_zero]
      intro hzmem
      exact hzroot (by
        simpa [data] using hA.mem_roots_of_mem_groupedRootList hzmem)
    have hroots : data.roots.count z = 0 := by
      exact Multiset.count_eq_zero.mpr hzroot
    rw [hgroup, hroots]

/-- Multiset form of `groupedRootList_count_eq_roots`, identifying the source
grouped root list with the canonical root multiset [GSLW19,
BlockHam.tex:450-480]. -/
theorem SourceHypotheses.groupedRootList_multiset_eq_roots
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    ((hA.rootProductData).groupedRootList : Multiset ℂ) =
      (hA.rootProductData).roots := by
  ext z
  simpa using hA.groupedRootList_count_eq_roots z

/-- Canonical complex root factorization regrouped into the source displayed
product [GSLW19, BlockHam.tex:450-480]. -/
theorem SourceHypotheses.realPolynomialToComplex_eq_sourceProduct
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    realPolynomialToComplex A =
      Polynomial.C ((hA.rootProductData.sourceConstant : ℝ) : ℂ) *
        (X : ℂ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
        (hA.rootProductData.interiorRealRootPairParameters.map fun s : ℝ =>
          (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod *
        (hA.rootProductData.outsideRealRoots.map fun s : OutsideRealRoot =>
          -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
            ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod *
        (hA.rootProductData.imaginaryRootParameters.map fun r : ℝ =>
          ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
            ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod *
        (hA.rootProductData.complexRootParameters.map fun z : ℝ × ℝ =>
          ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
            (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod := by
  classical
  let data := hA.rootProductData
  let factor : ℂ → ℂ[X] := fun z => (X : ℂ[X]) - Polynomial.C z
  have hmultiset :
      (((data.groupedRootList : Multiset ℂ).map factor).prod =
        (data.roots.map factor).prod) := by
    rw [hA.groupedRootList_multiset_eq_roots]
  have hrootProduct :
      realPolynomialToComplex A =
        Polynomial.C (realPolynomialToComplex A).leadingCoeff *
          (data.groupedRootList.map factor).prod := by
    calc
      realPolynomialToComplex A =
          Polynomial.C (realPolynomialToComplex A).leadingCoeff *
            (data.roots.map factor).prod := by
        simpa [data, factor] using data.product_eq
      _ =
          Polynomial.C (realPolynomialToComplex A).leadingCoeff *
            (data.groupedRootList.map factor).prod := by
        rw [← hmultiset]
        simp [factor]
  have hgrouped := data.groupedRootList_linearFactorProduct
  have hsourceGrouped :=
    SourceRootProductData.realPolynomialToComplex_sourceProductNotation_grouped_sourceConstant data
  have hsource :=
    realPolynomialToComplex_sourceProductNotation data.sourceConstant
      data.zeroRootPairs data.interiorRealRootPairParameters data.outsideRealRoots
      data.imaginaryRootParameters data.complexRootParameters
  calc
    realPolynomialToComplex A =
        Polynomial.C (realPolynomialToComplex A).leadingCoeff *
          (data.groupedRootList.map factor).prod := hrootProduct
    _ =
        Polynomial.C (realPolynomialToComplex A).leadingCoeff *
          ((X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
            (data.positiveInteriorRealRootValues.map fun s : ℝ =>
              (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
                ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
                  (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
            (data.positiveOutsideRealRootValues.map fun s : ℝ =>
              (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
                ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^
                  (realPolynomialToComplex A).rootMultiplicity (s : ℂ)).prod *
            (data.positiveImaginaryRootValues.map fun r : ℝ =>
              (((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
                ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))) ^
                  (realPolynomialToComplex A).rootMultiplicity
                    (Complex.I * (r : ℂ))).prod *
            (data.firstQuadrantComplexRootRepresentatives.map fun z : ℂ =>
              (((complexRootOrbit z).map
                (fun w => (X : ℂ[X]) - Polynomial.C w)).prod) ^
                  (realPolynomialToComplex A).rootMultiplicity z).prod) := by
      rw [hgrouped]
    _ =
        Polynomial.C ((data.sourceConstant : ℝ) : ℂ) *
          (X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
          (data.interiorRealRootPairParameters.map fun s : ℝ =>
            (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod *
          (data.outsideRealRoots.map fun s : OutsideRealRoot =>
            -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod *
          (data.imaginaryRootParameters.map fun r : ℝ =>
            ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
              ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod *
          (data.complexRootParameters.map fun z : ℝ × ℝ =>
            ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
              (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod := by
      simpa [mul_assoc] using hsourceGrouped.symm.trans hsource

namespace DegreeParityFactorCertificate

/-- Degree/parity certificate for a nonnegative real constant factor.  This
accounts for the nonnegative scalar multiplier in the root-class product proof
of [GSLW19, BlockHam.tex:436-480]. -/
noncomputable def nonnegativeConstant (c : ℝ) (hc : 0 ≤ c) :
    DegreeParityFactorCertificate where
  poly := Polynomial.C c
  degree := 0
  certificate :=
    { B := Polynomial.C (Real.sqrt c)
      C := 0
      eq_decomposition := by
        apply Polynomial.funext
        intro x
        simp [Polynomial.eval_pow, Real.sq_sqrt hc]
      degree_B := by
        rw [Polynomial.natDegree_C]
      degree_C := by
        simp
      parity_B := hasRealParity_C (Real.sqrt c) (by rfl)
      parity_C := hasRealParity_zero 1 }

/-- Degree/parity certificate for a pair of zero roots.  This is the
`x^{|S_0|/2}` pure-square contribution in the source proof
[GSLW19, BlockHam.tex:442-452,469-474]. -/
noncomputable def zeroRootPair : DegreeParityFactorCertificate where
  poly := X ^ 2
  degree := 1
  certificate :=
    DegreeParityCertificate.ofSquare X (by rw [Polynomial.natDegree_X])
      (by simpa [pow_one] using hasRealParity_X_pow 1)

/-- Degree/parity certificate for a pair of identical positive roots inside
the interval.  The source proof groups such roots in even multiplicity, so each
paired contribution is the pure square `(x^2-s^2)^2`
[GSLW19, BlockHam.tex:445,469-474]. -/
noncomputable def interiorRealRootPair (s : ℝ) : DegreeParityFactorCertificate where
  poly := (X ^ 2 - Polynomial.C (s ^ 2)) ^ 2
  degree := 2
  certificate :=
    DegreeParityCertificate.ofSquare (X ^ 2 - Polynomial.C (s ^ 2)) (by
      have hX : ((X : ℝ[X]) ^ 2).natDegree ≤ 2 := by
        rw [Polynomial.natDegree_X_pow]
      have hC : (Polynomial.C (s ^ 2) : ℝ[X]).natDegree ≤ 2 := by
        rw [Polynomial.natDegree_C]
        norm_num
      exact Polynomial.natDegree_sub_le_of_le hX hC)
      (by
        have hX : HasRealParity ((X : ℝ[X]) ^ 2) 2 := hasRealParity_X_pow 2
        have hC : HasRealParity (Polynomial.C (s ^ 2) : ℝ[X]) 2 :=
          hasRealParity_C (s ^ 2) (by norm_num)
        exact hX.sub hC)

/-- The source padding factor
`(x+i sqrt(1-x^2))(x+i sqrt(1-x^2))^* = 1`, used to raise degree/parity
without changing the represented nonnegative polynomial
[GSLW19, BlockHam.tex:479]. -/
noncomputable def unitParityPadding : DegreeParityFactorCertificate where
  poly := 1
  degree := 1
  certificate :=
    { B := X
      C := 1
      eq_decomposition := by ring
      degree_B := by rw [Polynomial.natDegree_X]
      degree_C := by
        rw [Polynomial.natDegree_one]
        norm_num
      parity_B := by simpa [pow_one] using hasRealParity_X_pow 1
      parity_C := hasRealParity_one (by norm_num) }

/-- Degree/parity certificate for the real-root factor outside the unit
interval [GSLW19, BlockHam.tex:459-460]. -/
noncomputable def realRoot (s : ℝ) (hs : 1 ≤ s ^ 2) :
    DegreeParityFactorCertificate where
  poly := Polynomial.C (s ^ 2) - X ^ 2
  degree := 1
  certificate :=
    let cert := realRootFactorCertificate s hs
    { B := cert.B
      C := cert.C
      eq_decomposition := cert.eq_decomposition
      degree_B := by
        change (Polynomial.C (Real.sqrt (s ^ 2 - 1)) * X).natDegree ≤ 1
        exact (Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [Polynomial.natDegree_X])
      degree_C := by
        change (Polynomial.C s).natDegree ≤ 1
        rw [Polynomial.natDegree_C]
        norm_num
      parity_B := by
        change HasRealParity (Polynomial.C (Real.sqrt (s ^ 2 - 1)) * X) 1
        simpa [pow_one] using
          ((hasRealParity_X_pow 1).C_mul (Real.sqrt (s ^ 2 - 1)))
      parity_C := by
        change HasRealParity (Polynomial.C s) 2
        exact hasRealParity_C s (by norm_num) }

/-- Degree/parity certificate for an imaginary-root pair factor
[GSLW19, BlockHam.tex:461]. -/
noncomputable def imaginaryRoot (r : ℝ) :
    DegreeParityFactorCertificate where
  poly := X ^ 2 + Polynomial.C (r ^ 2)
  degree := 1
  certificate :=
    let cert := imaginaryRootFactorCertificate r
    { B := cert.B
      C := cert.C
      eq_decomposition := cert.eq_decomposition
      degree_B := by
        change (Polynomial.C (Real.sqrt (r ^ 2 + 1)) * X).natDegree ≤ 1
        exact (Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [Polynomial.natDegree_X])
      degree_C := by
        change (Polynomial.C r).natDegree ≤ 1
        rw [Polynomial.natDegree_C]
        norm_num
      parity_B := by
        change HasRealParity (Polynomial.C (Real.sqrt (r ^ 2 + 1)) * X) 1
        simpa [pow_one] using
          ((hasRealParity_X_pow 1).C_mul (Real.sqrt (r ^ 2 + 1)))
      parity_C := by
        change HasRealParity (Polynomial.C r) 2
        exact hasRealParity_C r (by norm_num) }

/-- Degree/parity certificate for the complex-root quartic factor
[GSLW19, BlockHam.tex:462-466]. -/
noncomputable def complexRoot (a b : ℝ) :
    DegreeParityFactorCertificate where
  poly :=
    X ^ 4 + Polynomial.C (2 * (b ^ 2 - a ^ 2)) * X ^ 2 +
      Polynomial.C ((a ^ 2 + b ^ 2) ^ 2)
  degree := 2
  certificate :=
    let cert := complexRootFactorCertificateExplicit a b
    { B := cert.B
      C := cert.C
      eq_decomposition := cert.eq_decomposition
      degree_B := by
        change
          (Polynomial.C (complexRootParameter a b) * X ^ 2 -
            Polynomial.C (a ^ 2 + b ^ 2)).natDegree ≤ 2
        have hleft :
            (Polynomial.C (complexRootParameter a b) * (X : ℝ[X]) ^ 2).natDegree ≤ 2 :=
          (Polynomial.natDegree_C_mul_le _ _).trans (by rw [Polynomial.natDegree_X_pow])
        have hright : (Polynomial.C (a ^ 2 + b ^ 2) : ℝ[X]).natDegree ≤ 2 := by
          rw [Polynomial.natDegree_C]
          norm_num
        exact (Polynomial.natDegree_sub_le_of_le
          (p := Polynomial.C (complexRootParameter a b) * (X : ℝ[X]) ^ 2)
          (q := Polynomial.C (a ^ 2 + b ^ 2))
          (m := 2) (n := 2) hleft hright).trans (by simp)
      degree_C := by
        change
          (Polynomial.C (Real.sqrt ((complexRootParameter a b) ^ 2 - 1)) * X).natDegree ≤ 2
        exact ((Polynomial.natDegree_C_mul_le _ _).trans
          (by rw [Polynomial.natDegree_X])).trans (by norm_num)
      parity_B := by
        change
          HasRealParity
            (Polynomial.C (complexRootParameter a b) * X ^ 2 -
              Polynomial.C (a ^ 2 + b ^ 2)) 2
        have hleft :
            HasRealParity (Polynomial.C (complexRootParameter a b) * X ^ 2) 2 :=
          (hasRealParity_X_pow 2).C_mul (complexRootParameter a b)
        have hright :
            HasRealParity (Polynomial.C (a ^ 2 + b ^ 2)) 2 :=
          hasRealParity_C (a ^ 2 + b ^ 2) (by norm_num)
        exact hleft.sub hright
      parity_C := by
        change
          HasRealParity
            (Polynomial.C (Real.sqrt ((complexRootParameter a b) ^ 2 - 1)) * X) 3
        have h :
            HasRealParity
              (Polynomial.C (Real.sqrt ((complexRootParameter a b) ^ 2 - 1)) * X) 1 :=
          by
            simpa [pow_one] using
              ((hasRealParity_X_pow 1).C_mul
                (Real.sqrt ((complexRootParameter a b) ^ 2 - 1)))
        exact h.congr (by omega) }

/-- Product polynomial represented by a list of degree/parity source factors. -/
noncomputable def productPoly : List DegreeParityFactorCertificate → ℝ[X]
  | [] => 1
  | factor :: factors => factor.poly * productPoly factors

/-- Product polynomials multiply over list append. -/
@[simp]
theorem productPoly_append :
    ∀ factors more : List DegreeParityFactorCertificate,
      productPoly (factors ++ more) = productPoly factors * productPoly more
  | [], more => by simp [productPoly]
  | factor :: factors, more => by
      simp [productPoly, productPoly_append factors more, mul_assoc]

/-- Degree contribution represented by a list of degree/parity source factors. -/
def productDegree : List DegreeParityFactorCertificate → ℕ
  | [] => 0
  | factor :: factors => factor.degree + productDegree factors

/-- Padding factors contribute no polynomial content. -/
@[simp]
theorem productPoly_replicate_unitParityPadding :
    ∀ k : ℕ, productPoly (List.replicate k unitParityPadding) = 1
  | 0 => by simp [productPoly]
  | k + 1 => by
      change unitParityPadding.poly *
          productPoly (List.replicate k unitParityPadding) = 1
      rw [productPoly_replicate_unitParityPadding k]
      simp [unitParityPadding]

/-- Paired zero-root factors contribute `x^(2k)` to the source root product. -/
@[simp]
theorem productPoly_replicate_zeroRootPair :
    ∀ k : ℕ, productPoly (List.replicate k zeroRootPair) = (X : ℝ[X]) ^ (2 * k)
  | 0 => by simp [productPoly]
  | k + 1 => by
      change zeroRootPair.poly *
          productPoly (List.replicate k zeroRootPair) = (X : ℝ[X]) ^ (2 * (k + 1))
      rw [productPoly_replicate_zeroRootPair k]
      change (X : ℝ[X]) ^ 2 * (X : ℝ[X]) ^ (2 * k) = (X : ℝ[X]) ^ (2 * (k + 1))
      rw [← pow_add]
      have hexp : 2 + 2 * k = 2 * (k + 1) := by omega
      rw [hexp]

/-- Product notation for paired interior real roots, matching the
`S_(0,1)` factor in [GSLW19, BlockHam.tex:452-454,469-474]. -/
@[simp]
theorem productPoly_map_interiorRealRootPair :
    ∀ roots : List ℝ,
      productPoly (roots.map interiorRealRootPair) =
        (roots.map fun s => ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod
  | [] => by simp [productPoly]
  | s :: roots => by
      simp [productPoly, interiorRealRootPair, productPoly_map_interiorRealRootPair roots]

/-- Product notation for outside real roots, matching the
`S_[1,∞)` factor in [GSLW19, BlockHam.tex:454,459-460]. -/
@[simp]
theorem productPoly_map_realRoot :
    ∀ roots : List OutsideRealRoot,
      productPoly (roots.map (fun s => realRoot s.value s.outside)) =
        (roots.map fun s => Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod
  | [] => by simp [productPoly]
  | s :: roots => by
      change
        (Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2) *
            productPoly (roots.map (fun s => realRoot s.value s.outside)) =
          (Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2) *
            (roots.map fun s => Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod
      rw [productPoly_map_realRoot roots]

/-- Product notation for imaginary-root representatives, matching the `S_I`
factor in [GSLW19, BlockHam.tex:455,461]. -/
@[simp]
theorem productPoly_map_imaginaryRoot :
    ∀ roots : List ℝ,
      productPoly (roots.map imaginaryRoot) =
        (roots.map fun r => (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod
  | [] => by simp [productPoly]
  | r :: roots => by
      simp [productPoly, imaginaryRoot, productPoly_map_imaginaryRoot roots]

/-- Product notation for non-real quartets, matching the `S_C` factor in
[GSLW19, BlockHam.tex:456,462-466]. -/
@[simp]
theorem productPoly_map_complexRoot :
    ∀ roots : List (ℝ × ℝ),
      productPoly (roots.map (fun z => complexRoot z.1 z.2)) =
        (roots.map fun z =>
          (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
            Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod
  | [] => by simp [productPoly]
  | z :: roots => by
      change
        ((X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
            Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)) *
            productPoly (roots.map (fun z => complexRoot z.1 z.2)) =
          ((X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
            Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)) *
            (roots.map fun z =>
              (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
                Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod
      rw [productPoly_map_complexRoot roots]

/-- Padding factors contribute exactly one degree/parity step each. -/
@[simp]
theorem productDegree_replicate_unitParityPadding :
    ∀ k : ℕ, productDegree (List.replicate k unitParityPadding) = k
  | 0 => by simp [productDegree]
  | k + 1 => by
      change unitParityPadding.degree +
          productDegree (List.replicate k unitParityPadding) = k + 1
      rw [productDegree_replicate_unitParityPadding k]
      simp [unitParityPadding]
      omega

@[simp]
theorem productDegree_replicate_zeroRootPair :
    ∀ k : ℕ, productDegree (List.replicate k zeroRootPair) = k
  | 0 => by simp [productDegree]
  | k + 1 => by
      change zeroRootPair.degree +
          productDegree (List.replicate k zeroRootPair) = k + 1
      rw [productDegree_replicate_zeroRootPair k]
      change 1 + k = k + 1
      omega

@[simp]
theorem productDegree_append :
    ∀ factors more : List DegreeParityFactorCertificate,
      productDegree (factors ++ more) = productDegree factors + productDegree more
  | [], more => by simp [productDegree]
  | factor :: factors, more => by
      simp [productDegree, productDegree_append factors more]
      omega

@[simp]
theorem productDegree_map_interiorRealRootPair :
    ∀ roots : List ℝ,
      productDegree (roots.map interiorRealRootPair) = 2 * roots.length
  | [] => by simp [productDegree]
  | _ :: roots => by
      simp [productDegree, interiorRealRootPair, productDegree_map_interiorRealRootPair roots]
      omega

@[simp]
theorem productDegree_map_realRoot :
    ∀ roots : List OutsideRealRoot,
      productDegree (roots.map (fun s => realRoot s.value s.outside)) = roots.length
  | [] => by simp [productDegree]
  | _ :: roots => by
      change 1 + productDegree (roots.map (fun s => realRoot s.value s.outside)) =
        roots.length + 1
      rw [productDegree_map_realRoot roots]
      omega

@[simp]
theorem productDegree_map_imaginaryRoot :
    ∀ roots : List ℝ,
      productDegree (roots.map imaginaryRoot) = roots.length
  | [] => by simp [productDegree]
  | _ :: roots => by
      simp [productDegree, imaginaryRoot, productDegree_map_imaginaryRoot roots]
      omega

@[simp]
theorem productDegree_map_complexRoot :
    ∀ roots : List (ℝ × ℝ),
      productDegree (roots.map (fun z => complexRoot z.1 z.2)) = 2 * roots.length
  | [] => by simp [productDegree]
  | _ :: roots => by
      change 2 + productDegree (roots.map (fun z => complexRoot z.1 z.2)) =
        2 * (roots.length + 1)
      rw [productDegree_map_complexRoot roots]
      omega

/-- Degree/parity product closure for source factor certificates
[GSLW19, BlockHam.tex:475-480]. -/
noncomputable def productCertificate :
    (factors : List DegreeParityFactorCertificate) →
      DegreeParityCertificate (productPoly factors) (productDegree factors)
  | [] => DegreeParityCertificate.one
  | factor :: factors =>
      DegreeParityCertificate.mul factor.certificate (productCertificate factors)

end DegreeParityFactorCertificate

/-- A source-style factorization into root-class factors that already carry the
degree/parity data required by the real-polynomial completion theorem. -/
structure DegreeParityProductDecomposition (A : ℝ[X]) (k : ℕ) where
  /-- Degree/parity factors whose product represents `A`. -/
  factors : List DegreeParityFactorCertificate
  product_eq : A = DegreeParityFactorCertificate.productPoly factors
  degree_eq : DegreeParityFactorCertificate.productDegree factors = k

namespace DegreeParityProductDecomposition

/-- A degree/parity source product decomposition yields the exact certificate
needed by the QSP completion layer. -/
noncomputable def toCertificate {A : ℝ[X]} {k : ℕ}
    (h : DegreeParityProductDecomposition A k) :
    DegreeParityCertificate A k :=
  let cert := DegreeParityFactorCertificate.productCertificate h.factors
  { B := cert.B
    C := cert.C
    eq_decomposition := by
      exact h.product_eq.trans cert.eq_decomposition
    degree_B := by
      simpa [h.degree_eq] using cert.degree_B
    degree_C := by
      simpa [h.degree_eq] using cert.degree_C
    parity_B := by
      simpa [h.degree_eq] using cert.parity_B
    parity_C := by
      simpa [h.degree_eq] using cert.parity_C }

end DegreeParityProductDecomposition

/-- Root-class factors from the source proof, converted into the degree/parity
certificate factors proved above.  Zero roots and roots in `(0,1)` are supplied
as already paired factors, reflecting the source observation that their
multipities are even under interval nonnegativity [GSLW19,
BlockHam.tex:442-456,469-474]. -/
noncomputable def sourceRootClassFactorList
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (zeroRootPairs paddingFactors : ℕ) (interiorRootPairs : List ℝ)
    (outsideRealRoots : List OutsideRealRoot) (imaginaryRoots : List ℝ)
    (complexRoots : List (ℝ × ℝ)) :
    List DegreeParityFactorCertificate :=
  [DegreeParityFactorCertificate.nonnegativeConstant constant constant_nonnegative] ++
    List.replicate zeroRootPairs DegreeParityFactorCertificate.zeroRootPair ++
    List.replicate paddingFactors DegreeParityFactorCertificate.unitParityPadding ++
    interiorRootPairs.map DegreeParityFactorCertificate.interiorRealRootPair ++
    outsideRealRoots.map (fun s =>
      DegreeParityFactorCertificate.realRoot s.value s.outside) ++
    imaginaryRoots.map DegreeParityFactorCertificate.imaginaryRoot ++
    complexRoots.map (fun z => DegreeParityFactorCertificate.complexRoot z.1 z.2)

/-- Degree accounting for the source root-class factor list.  This is the Lean
counterpart of the `|S|/2` degree count used in [GSLW19,
BlockHam.tex:469-479]. -/
theorem productDegree_sourceRootClassFactorList
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (zeroRootPairs paddingFactors : ℕ) (interiorRootPairs : List ℝ)
    (outsideRealRoots : List OutsideRealRoot) (imaginaryRoots : List ℝ)
    (complexRoots : List (ℝ × ℝ)) :
    DegreeParityFactorCertificate.productDegree
      (sourceRootClassFactorList constant constant_nonnegative zeroRootPairs paddingFactors
        interiorRootPairs outsideRealRoots imaginaryRoots complexRoots) =
      zeroRootPairs + paddingFactors + 2 * interiorRootPairs.length +
        outsideRealRoots.length + imaginaryRoots.length + 2 * complexRoots.length := by
  simp [sourceRootClassFactorList, DegreeParityFactorCertificate.productDegree,
    DegreeParityFactorCertificate.nonnegativeConstant,
    DegreeParityFactorCertificate.productDegree_append,
    DegreeParityFactorCertificate.productDegree_replicate_zeroRootPair,
    DegreeParityFactorCertificate.productDegree_replicate_unitParityPadding,
    DegreeParityFactorCertificate.productDegree_map_interiorRealRootPair,
    DegreeParityFactorCertificate.productDegree_map_realRoot,
    DegreeParityFactorCertificate.productDegree_map_imaginaryRoot,
    DegreeParityFactorCertificate.productDegree_map_complexRoot]
  omega

/-- Polynomial content of the source root-class factor list after removing the
unit padding factors.  This is the product bookkeeping behind [GSLW19,
BlockHam.tex:450-456,469-479]. -/
theorem productPoly_sourceRootClassFactorList
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (zeroRootPairs paddingFactors : ℕ) (interiorRootPairs : List ℝ)
    (outsideRealRoots : List OutsideRealRoot) (imaginaryRoots : List ℝ)
    (complexRoots : List (ℝ × ℝ)) :
    DegreeParityFactorCertificate.productPoly
      (sourceRootClassFactorList constant constant_nonnegative zeroRootPairs paddingFactors
        interiorRootPairs outsideRealRoots imaginaryRoots complexRoots) =
      Polynomial.C constant *
        (X : ℝ[X]) ^ (2 * zeroRootPairs) *
        DegreeParityFactorCertificate.productPoly
          (interiorRootPairs.map DegreeParityFactorCertificate.interiorRealRootPair) *
        DegreeParityFactorCertificate.productPoly
          (outsideRealRoots.map (fun s =>
            DegreeParityFactorCertificate.realRoot s.value s.outside)) *
        DegreeParityFactorCertificate.productPoly
          (imaginaryRoots.map DegreeParityFactorCertificate.imaginaryRoot) *
        DegreeParityFactorCertificate.productPoly
          (complexRoots.map (fun z => DegreeParityFactorCertificate.complexRoot z.1 z.2)) := by
  simp [sourceRootClassFactorList, DegreeParityFactorCertificate.productPoly,
    DegreeParityFactorCertificate.productPoly_append,
    DegreeParityFactorCertificate.nonnegativeConstant,
    DegreeParityFactorCertificate.productPoly_replicate_zeroRootPair,
    DegreeParityFactorCertificate.productPoly_replicate_unitParityPadding]
  ring

namespace SourceRootProductData

/-- The non-scalar part of the source root-class product.  It is represented
through the same source factors as the final decomposition, with scalar
coefficient `1`; this lets the constant-sign proof reuse the existing
interval-square certificate API [GSLW19, BlockHam.tex:450-480]. -/
noncomputable def sourceProductTail {A : ℝ[X]} (data : SourceRootProductData A) :
    ℝ[X] :=
  DegreeParityFactorCertificate.productPoly
    (sourceRootClassFactorList (1 : ℝ) (by norm_num : 0 ≤ (1 : ℝ))
      data.zeroRootPairs 0 data.interiorRealRootPairParameters data.outsideRealRoots
      data.imaginaryRootParameters data.complexRootParameters)

/-- The source-product tail has an interval-square certificate because it is
the product of the certified non-scalar source root-class factors. -/
noncomputable def sourceProductTailCertificate {A : ℝ[X]}
    (data : SourceRootProductData A) : Certificate data.sourceProductTail :=
  (DegreeParityFactorCertificate.productCertificate
    (sourceRootClassFactorList (1 : ℝ) (by norm_num : 0 ≤ (1 : ℝ))
      data.zeroRootPairs 0 data.interiorRealRootPairParameters data.outsideRealRoots
      data.imaginaryRootParameters data.complexRootParameters)).toCertificate

/-- The source-product tail is nonnegative on the source interval. -/
theorem sourceProductTail_nonnegativeOnUnitInterval {A : ℝ[X]}
    (data : SourceRootProductData A) :
    NonnegativeOnUnitInterval data.sourceProductTail :=
  nonnegativeOnUnitInterval_of_certificate data.sourceProductTailCertificate

/-- Expanding `sourceProductTail` removes the scalar coefficient and padding
unit factors. -/
theorem sourceProductTail_eq_sourceNotation {A : ℝ[X]}
    (data : SourceRootProductData A) :
    data.sourceProductTail =
      (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
        (data.interiorRealRootPairParameters.map fun s =>
          ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
        (data.outsideRealRoots.map fun s =>
          Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
        (data.imaginaryRootParameters.map fun r =>
          (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
        (data.complexRootParameters.map fun z =>
          (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
            Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod := by
  simp [sourceProductTail, productPoly_sourceRootClassFactorList,
    DegreeParityFactorCertificate.productPoly_map_interiorRealRootPair,
    DegreeParityFactorCertificate.productPoly_map_realRoot,
    DegreeParityFactorCertificate.productPoly_map_imaginaryRoot,
    DegreeParityFactorCertificate.productPoly_map_complexRoot]

end SourceRootProductData

/-- The source displayed product factors as the sign-corrected scalar
`sourceConstant` times the certified non-scalar tail. -/
theorem SourceHypotheses.sourceProduct_eq_sourceConstant_mul_tail
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    A =
      Polynomial.C hA.rootProductData.sourceConstant *
        hA.rootProductData.sourceProductTail := by
  classical
  let data := hA.rootProductData
  apply realPolynomialToComplex_injective
  have hsource := hA.realPolynomialToComplex_eq_sourceProduct
  have hnotation :=
    realPolynomialToComplex_sourceProductNotation data.sourceConstant
      data.zeroRootPairs data.interiorRealRootPairParameters data.outsideRealRoots
      data.imaginaryRootParameters data.complexRootParameters
  have htail_complex :
      realPolynomialToComplex
          (Polynomial.C data.sourceConstant * data.sourceProductTail) =
        Polynomial.C ((data.sourceConstant : ℝ) : ℂ) *
          (X : ℂ[X]) ^ (2 * data.zeroRootPairs) *
          (data.interiorRealRootPairParameters.map fun s : ℝ =>
            (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod *
          (data.outsideRealRoots.map fun s : OutsideRealRoot =>
            -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod *
          (data.imaginaryRootParameters.map fun r : ℝ =>
            ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
              ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod *
          (data.complexRootParameters.map fun z : ℝ × ℝ =>
            ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
              (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod := by
    rw [SourceRootProductData.sourceProductTail_eq_sourceNotation]
    simpa [mul_assoc] using hnotation
  exact hsource.trans htail_complex.symm

/-- The source scalar is nonnegative.  The proof follows the final sign step of
the root-class product construction: choose an interior point avoiding the
finite root set of the certified tail, so the tail is strictly positive and
the interval nonnegativity of `A` forces the scalar to be nonnegative
[GSLW19, BlockHam.tex:475-480]. -/
theorem SourceHypotheses.sourceConstant_nonnegative
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    0 ≤ hA.rootProductData.sourceConstant := by
  classical
  let data := hA.rootProductData
  by_contra hnot
  have hconst_neg : data.sourceConstant < 0 := lt_of_not_ge hnot
  have hconst_ne : data.sourceConstant ≠ 0 := by linarith
  have hA_ne : A ≠ 0 := by
    intro hzero
    have hconst_zero : data.sourceConstant = 0 := by
      simp [data, SourceRootProductData.sourceConstant, hzero]
    exact hconst_ne hconst_zero
  have hproduct : A = Polynomial.C data.sourceConstant * data.sourceProductTail := by
    simpa [data] using hA.sourceProduct_eq_sourceConstant_mul_tail
  have htail_ne : data.sourceProductTail ≠ 0 := by
    intro htail_zero
    have hAzero : A = 0 := by
      rw [hproduct, htail_zero, mul_zero]
    exact hA_ne hAzero
  rcases exists_Ioo_not_root_of_ne_zero htail_ne
      (by norm_num : (-1 : ℝ) < 1) with ⟨x, hxIoo, htail_eval_ne⟩
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩
  have htail_nonneg :
      0 ≤ data.sourceProductTail.eval x :=
    data.sourceProductTail_nonnegativeOnUnitInterval x hxIcc
  have htail_pos : 0 < data.sourceProductTail.eval x :=
    lt_of_le_of_ne htail_nonneg (by
      intro hzero
      exact htail_eval_ne hzero.symm)
  have hA_eval_nonneg := hA.nonnegative x hxIcc
  have hA_eval :
      A.eval x = data.sourceConstant * data.sourceProductTail.eval x := by
    have h := congrArg (fun P : ℝ[X] => P.eval x) hproduct
    simpa [Polynomial.eval_mul] using h
  have hA_eval_neg : A.eval x < 0 := by
    rw [hA_eval]
    exact mul_neg_of_neg_of_pos hconst_neg htail_pos
  linarith

/-- Source-facing root-class factorization of the polynomial `A`.  This is the
formal counterpart of the product decomposition in [GSLW19,
BlockHam.tex:450-456]; the remaining hard theorem is to construct such a
factorization from `SourceHypotheses` using the roots of `A`. -/
structure SourceRootClassFactorization (A : ℝ[X]) (k : ℕ) where
  /-- Leading scalar in the source root-class product. -/
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  /-- Number of paired zero-root factors. -/
  zeroRootPairs : ℕ
  /-- Number of unit padding factors used to match the requested parity index. -/
  paddingFactors : ℕ
  /-- Representatives for paired real roots inside the unit interval. -/
  interiorRootPairs : List ℝ
  /-- Representatives for real roots outside the open unit interval. -/
  outsideRealRoots : List OutsideRealRoot
  /-- Representatives for purely imaginary root pairs. -/
  imaginaryRoots : List ℝ
  /-- Representatives for non-real, non-imaginary complex root classes. -/
  complexRoots : List (ℝ × ℝ)
  product_eq :
    A = DegreeParityFactorCertificate.productPoly
      (sourceRootClassFactorList constant constant_nonnegative zeroRootPairs paddingFactors
        interiorRootPairs outsideRealRoots imaginaryRoots complexRoots)
  degree_eq :
    DegreeParityFactorCertificate.productDegree
      (sourceRootClassFactorList constant constant_nonnegative zeroRootPairs paddingFactors
        interiorRootPairs outsideRealRoots imaginaryRoots complexRoots) = k

namespace SourceRootClassFactorization

/-- Build a source root-class factorization from the expanded product and the
expanded degree count.  This is the convenient constructor for the root-grouping
step in [GSLW19, BlockHam.tex:450-479]: after the roots have been classified,
only the displayed product identity and the `|S|/2` count remain to be proved. -/
noncomputable def ofExpanded {A : ℝ[X]} {k : ℕ}
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (zeroRootPairs paddingFactors : ℕ) (interiorRootPairs : List ℝ)
    (outsideRealRoots : List OutsideRealRoot) (imaginaryRoots : List ℝ)
    (complexRoots : List (ℝ × ℝ))
    (hproduct :
      A =
        Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (interiorRootPairs.map DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (imaginaryRoots.map DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (complexRoots.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree :
      zeroRootPairs + paddingFactors + 2 * interiorRootPairs.length +
          outsideRealRoots.length + imaginaryRoots.length +
            2 * complexRoots.length = k) :
    SourceRootClassFactorization A k where
  constant := constant
  constant_nonnegative := constant_nonnegative
  zeroRootPairs := zeroRootPairs
  paddingFactors := paddingFactors
  interiorRootPairs := interiorRootPairs
  outsideRealRoots := outsideRealRoots
  imaginaryRoots := imaginaryRoots
  complexRoots := complexRoots
  product_eq := by
    rw [productPoly_sourceRootClassFactorList]
    exact hproduct
  degree_eq := by
    rw [productDegree_sourceRootClassFactorList]
    exact hdegree

/-- Expanded polynomial product corresponding to the source root classes
[GSLW19, BlockHam.tex:450-456]. -/
theorem product_eq_expanded {A : ℝ[X]} {k : ℕ}
    (h : SourceRootClassFactorization A k) :
    A =
      Polynomial.C h.constant *
        (X : ℝ[X]) ^ (2 * h.zeroRootPairs) *
        DegreeParityFactorCertificate.productPoly
          (h.interiorRootPairs.map DegreeParityFactorCertificate.interiorRealRootPair) *
        DegreeParityFactorCertificate.productPoly
          (h.outsideRealRoots.map (fun s =>
            DegreeParityFactorCertificate.realRoot s.value s.outside)) *
        DegreeParityFactorCertificate.productPoly
          (h.imaginaryRoots.map DegreeParityFactorCertificate.imaginaryRoot) *
        DegreeParityFactorCertificate.productPoly
          (h.complexRoots.map (fun z => DegreeParityFactorCertificate.complexRoot z.1 z.2)) := by
  calc
    A = DegreeParityFactorCertificate.productPoly
        (sourceRootClassFactorList h.constant h.constant_nonnegative h.zeroRootPairs
          h.paddingFactors h.interiorRootPairs h.outsideRealRoots h.imaginaryRoots
          h.complexRoots) := h.product_eq
    _ =
      Polynomial.C h.constant *
        (X : ℝ[X]) ^ (2 * h.zeroRootPairs) *
        DegreeParityFactorCertificate.productPoly
          (h.interiorRootPairs.map DegreeParityFactorCertificate.interiorRealRootPair) *
        DegreeParityFactorCertificate.productPoly
          (h.outsideRealRoots.map (fun s =>
            DegreeParityFactorCertificate.realRoot s.value s.outside)) *
        DegreeParityFactorCertificate.productPoly
          (h.imaginaryRoots.map DegreeParityFactorCertificate.imaginaryRoot) *
        DegreeParityFactorCertificate.productPoly
          (h.complexRoots.map (fun z => DegreeParityFactorCertificate.complexRoot z.1 z.2)) :=
        productPoly_sourceRootClassFactorList h.constant h.constant_nonnegative
          h.zeroRootPairs h.paddingFactors h.interiorRootPairs h.outsideRealRoots
          h.imaginaryRoots h.complexRoots

/-- Source-notation expansion of the root-class product, matching the displayed
formula for `A(x)` in [GSLW19, BlockHam.tex:452-456]. -/
theorem product_eq_sourceNotation {A : ℝ[X]} {k : ℕ}
    (h : SourceRootClassFactorization A k) :
    A =
      Polynomial.C h.constant *
        (X : ℝ[X]) ^ (2 * h.zeroRootPairs) *
        (h.interiorRootPairs.map fun s =>
          ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
        (h.outsideRealRoots.map fun s =>
          Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
        (h.imaginaryRoots.map fun r =>
          (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
        (h.complexRoots.map fun z =>
          (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
            Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod := by
  simpa using h.product_eq_expanded

/-- Degree accounting extracted from the source root-class factorization
[GSLW19, BlockHam.tex:469-479]. -/
theorem degree_count {A : ℝ[X]} {k : ℕ}
    (h : SourceRootClassFactorization A k) :
    h.zeroRootPairs + h.paddingFactors + 2 * h.interiorRootPairs.length +
        h.outsideRealRoots.length + h.imaginaryRoots.length +
          2 * h.complexRoots.length = k := by
  calc
    h.zeroRootPairs + h.paddingFactors + 2 * h.interiorRootPairs.length +
        h.outsideRealRoots.length + h.imaginaryRoots.length +
          2 * h.complexRoots.length =
      DegreeParityFactorCertificate.productDegree
        (sourceRootClassFactorList h.constant h.constant_nonnegative h.zeroRootPairs
          h.paddingFactors h.interiorRootPairs h.outsideRealRoots h.imaginaryRoots
          h.complexRoots) :=
        (productDegree_sourceRootClassFactorList h.constant h.constant_nonnegative
          h.zeroRootPairs h.paddingFactors h.interiorRootPairs h.outsideRealRoots
          h.imaginaryRoots h.complexRoots).symm
    _ = k := h.degree_eq

/-- The zero-polynomial case of the source proof [GSLW19,
BlockHam.tex:441].  Padding factors adjust the requested parity/degree without
changing the represented polynomial. -/
noncomputable def zero (k : ℕ) : SourceRootClassFactorization (0 : ℝ[X]) k where
  constant := 0
  constant_nonnegative := by norm_num
  zeroRootPairs := 0
  paddingFactors := k
  interiorRootPairs := []
  outsideRealRoots := []
  imaginaryRoots := []
  complexRoots := []
  product_eq := by
    simp [sourceRootClassFactorList,
      DegreeParityFactorCertificate.productPoly,
      DegreeParityFactorCertificate.nonnegativeConstant]
  degree_eq := by
    simp [sourceRootClassFactorList,
      DegreeParityFactorCertificate.productDegree,
      DegreeParityFactorCertificate.nonnegativeConstant]

/-- Nonnegative constant source-polynomial case.  This is the no-root
root-class product, with unit padding providing the requested degree/parity
index [GSLW19, BlockHam.tex:450-480]. -/
noncomputable def nonnegativeConstant (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    SourceRootClassFactorization (Polynomial.C c) k where
  constant := c
  constant_nonnegative := hc
  zeroRootPairs := 0
  paddingFactors := k
  interiorRootPairs := []
  outsideRealRoots := []
  imaginaryRoots := []
  complexRoots := []
  product_eq := by
    simp [sourceRootClassFactorList,
      DegreeParityFactorCertificate.productPoly,
      DegreeParityFactorCertificate.nonnegativeConstant]
  degree_eq := by
    simp [sourceRootClassFactorList,
      DegreeParityFactorCertificate.productDegree,
      DegreeParityFactorCertificate.nonnegativeConstant]

/-- The source root-class factorization is exactly the product decomposition
consumed by the QSP completion layer [GSLW19, BlockHam.tex:475-480]. -/
noncomputable def toProductDecomposition {A : ℝ[X]} {k : ℕ}
    (h : SourceRootClassFactorization A k) :
    DegreeParityProductDecomposition A k where
  factors :=
    sourceRootClassFactorList h.constant h.constant_nonnegative h.zeroRootPairs h.paddingFactors
      h.interiorRootPairs h.outsideRealRoots h.imaginaryRoots h.complexRoots
  product_eq := h.product_eq
  degree_eq := h.degree_eq

/-- The source root-class factorization yields the interval-square
degree/parity certificate. -/
noncomputable def toCertificate {A : ℝ[X]} {k : ℕ}
    (h : SourceRootClassFactorization A k) :
    DegreeParityCertificate A k :=
  h.toProductDecomposition.toCertificate

end SourceRootClassFactorization

/-- Constant-polynomial boundary of the source root-class construction
[GSLW19, BlockHam.tex:441-480].  The source proof treats the zero polynomial
separately and then factors the remaining roots.  When `natDegree A = 0`,
there are no nonconstant root classes to enumerate, so the nonnegative constant
certificate is the complete source product. -/
noncomputable def SourceHypotheses.factorizationOfNatDegreeEqZero
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) (hdeg : A.natDegree = 0) :
    SourceRootClassFactorization A k := by
  have hconst : A = Polynomial.C (A.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hnonneg : 0 ≤ A.coeff 0 := by
    have hzero : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> norm_num
    have hnonneg_eval : 0 ≤ A.eval 0 := hA.nonnegative 0 hzero
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hnonneg_eval
  exact hconst.symm ▸ SourceRootClassFactorization.nonnegativeConstant (A.coeff 0) hnonneg k

/-- Adapter from the automatic representative lists to the source root-class
factorization.  After the root multiset has been partitioned according to the
source classes, the remaining obligations are exactly the displayed product
identity and the `|S|/2` degree count [GSLW19, BlockHam.tex:450-480]. -/
noncomputable def SourceRootProductData.toSourceRootClassFactorizationOfExpanded
    {A : ℝ[X]} {k : ℕ} (data : SourceRootProductData A)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (zeroRootPairs paddingFactors : ℕ)
    (hproduct :
      A =
        Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree :
      zeroRootPairs + paddingFactors +
          2 * data.interiorRealRootPairParameters.length +
          data.outsideRealRoots.length + data.imaginaryRootParameters.length +
            2 * data.complexRootParameters.length = k) :
    SourceRootClassFactorization A k :=
  SourceRootClassFactorization.ofExpanded constant constant_nonnegative
    zeroRootPairs paddingFactors data.interiorRealRootPairParameters
    data.outsideRealRoots data.imaginaryRootParameters data.complexRootParameters
    hproduct hdegree

/-- Same adapter as `toSourceRootClassFactorizationOfExpanded`, but with the
zero-root pairs fixed to the count extracted from the source root facts and the
degree obligation phrased as `rootClassDegree + padding = k`. -/
noncomputable def SourceRootProductData.toSourceRootClassFactorizationOfRootClassDegree
    {A : ℝ[X]} {k : ℕ} (data : SourceRootProductData A)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (paddingFactors : ℕ)
    (hproduct :
      A =
        Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree : data.rootClassDegree + paddingFactors = k) :
    SourceRootClassFactorization A k :=
  data.toSourceRootClassFactorizationOfExpanded constant constant_nonnegative
    data.zeroRootPairs paddingFactors hproduct (by
      unfold SourceRootProductData.rootClassDegree at hdegree
      omega)

/-- Final proof obligations for the automatic root representatives selected
from `SourceRootProductData`.  This is the compact interface for the remaining
source-grouping step: prove the displayed product identity and the degree count
from the partition of the complex roots [GSLW19, BlockHam.tex:450-480]. -/
structure SourceRootClassCoverage {A : ℝ[X]} (data : SourceRootProductData A)
    (k : ℕ) where
  /-- Leading scalar in the completed source root-class product. -/
  constant : ℝ
  constant_nonnegative : 0 ≤ constant
  /-- Number of unit padding factors used to reach degree/parity index `k`. -/
  paddingFactors : ℕ
  product_eq :
    A =
      Polynomial.C constant *
        (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
        DegreeParityFactorCertificate.productPoly
          (data.interiorRealRootPairParameters.map
            DegreeParityFactorCertificate.interiorRealRootPair) *
        DegreeParityFactorCertificate.productPoly
          (data.outsideRealRoots.map (fun s =>
            DegreeParityFactorCertificate.realRoot s.value s.outside)) *
        DegreeParityFactorCertificate.productPoly
          (data.imaginaryRootParameters.map
            DegreeParityFactorCertificate.imaginaryRoot) *
        DegreeParityFactorCertificate.productPoly
          (data.complexRootParameters.map (fun z =>
            DegreeParityFactorCertificate.complexRoot z.1 z.2))
  degree_eq : data.rootClassDegree + paddingFactors = k

namespace SourceRootClassCoverage

/-- A completed root-class coverage package yields the source root-class
factorization consumed by QSP completion. -/
noncomputable def toSourceRootClassFactorization {A : ℝ[X]} {k : ℕ}
    {data : SourceRootProductData A} (coverage : SourceRootClassCoverage data k) :
    SourceRootClassFactorization A k :=
  data.toSourceRootClassFactorizationOfRootClassDegree coverage.constant
    coverage.constant_nonnegative coverage.paddingFactors coverage.product_eq
    coverage.degree_eq

/-- Build coverage by choosing the unit-padding count from the root-class
degree bound.  This is the final interface shape used by the source proof:
after the displayed product identity and `rootClassDegree <= k` are known,
padding by unit factors reaches degree/parity index `k`
[GSLW19, BlockHam.tex:469-480]. -/
noncomputable def ofProductEqAndDegreeLe {A : ℝ[X]} {k : ℕ}
    {data : SourceRootProductData A}
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      A =
        Polynomial.C constant *
          (X : ℝ[X]) ^ (2 * data.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (data.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (data.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (data.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (data.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree_le : data.rootClassDegree ≤ k) :
    SourceRootClassCoverage data k where
  constant := constant
  constant_nonnegative := constant_nonnegative
  paddingFactors := k - data.rootClassDegree
  product_eq := hproduct
  degree_eq := by
    exact Nat.add_sub_of_le hdegree_le

end SourceRootClassCoverage

/-- Source-hypothesis wrapper for the final root-class proof obligations:
the canonical root-product data, a displayed product identity, and the source
degree bound determine the root-class factorization [GSLW19,
BlockHam.tex:450-480]. -/
noncomputable def SourceHypotheses.factorizationOfProductEqAndDegreeLe
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      A =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hdegree_le : hA.rootProductData.rootClassDegree ≤ k) :
    SourceRootClassFactorization A k :=
  (SourceRootClassCoverage.ofProductEqAndDegreeLe
    (data := hA.rootProductData) (k := k)
    constant constant_nonnegative hproduct hdegree_le).toSourceRootClassFactorization

/-- Same source-hypothesis wrapper as
`factorizationOfProductEqAndDegreeLe`, but with the remaining degree
obligation stated in the source form `2*rootClassDegree <= |S|`
[GSLW19, BlockHam.tex:476-479]. -/
noncomputable def SourceHypotheses.factorizationOfProductEqAndRootCount
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      A =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)))
    (hcount :
      2 * hA.rootProductData.rootClassDegree ≤ hA.rootProductData.roots.card) :
    SourceRootClassFactorization A k :=
  hA.factorizationOfProductEqAndDegreeLe constant constant_nonnegative
    hproduct (hA.rootClassDegree_le_of_two_mul_le_roots_card hcount)

/-- Same source-hypothesis wrapper, now using the internally proved root-class
count bound.  After the displayed product identity is proved, the source count
`2*rootClassDegree <= |S|` is automatic [GSLW19, BlockHam.tex:476-479]. -/
noncomputable def SourceHypotheses.factorizationOfProductEq
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hproduct :
      A =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2))) :
    SourceRootClassFactorization A k :=
  hA.factorizationOfProductEqAndRootCount constant constant_nonnegative
    hproduct hA.two_mul_rootClassDegree_le_roots_card

/-- Complexified source-product equality is enough to build the interval-square
factorization.  This is the adapter used after grouping the canonical complex
root product into the displayed source classes of [GSLW19,
BlockHam.tex:452-480]. -/
noncomputable def SourceHypotheses.factorizationOfComplexProductEq
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k)
    (constant : ℝ) (constant_nonnegative : 0 ≤ constant)
    (hcomplex :
      realPolynomialToComplex A =
        Polynomial.C (constant : ℂ) *
          (X : ℂ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
          (hA.rootProductData.interiorRealRootPairParameters.map fun s : ℝ =>
            (((X : ℂ[X]) - Polynomial.C (s : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s : ℂ)))) ^ 2).prod *
          (hA.rootProductData.outsideRealRoots.map fun s : OutsideRealRoot =>
            -(((X : ℂ[X]) - Polynomial.C (s.value : ℂ)) *
              ((X : ℂ[X]) - Polynomial.C (-(s.value : ℂ))))).prod *
          (hA.rootProductData.imaginaryRootParameters.map fun r : ℝ =>
            ((X : ℂ[X]) - Polynomial.C (Complex.I * (r : ℂ))) *
              ((X : ℂ[X]) - Polynomial.C (-(Complex.I * (r : ℂ))))).prod *
          (hA.rootProductData.complexRootParameters.map fun z : ℝ × ℝ =>
            ((complexRootOrbit ((z.1 : ℂ) + Complex.I * (z.2 : ℂ))).map
              (fun w => (X : ℂ[X]) - Polynomial.C w)).prod).prod) :
    SourceRootClassFactorization A k := by
  have hsource :=
    realPolynomialToComplex_sourceProductNotation constant
      hA.rootProductData.zeroRootPairs
      hA.rootProductData.interiorRealRootPairParameters
      hA.rootProductData.outsideRealRoots
      hA.rootProductData.imaginaryRootParameters
      hA.rootProductData.complexRootParameters
  have hproduct :
      A =
        Polynomial.C constant *
          (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.interiorRealRootPairParameters.map
              DegreeParityFactorCertificate.interiorRealRootPair) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.outsideRealRoots.map (fun s =>
              DegreeParityFactorCertificate.realRoot s.value s.outside)) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.imaginaryRootParameters.map
              DegreeParityFactorCertificate.imaginaryRoot) *
          DegreeParityFactorCertificate.productPoly
            (hA.rootProductData.complexRootParameters.map (fun z =>
              DegreeParityFactorCertificate.complexRoot z.1 z.2)) := by
    apply realPolynomialToComplex_injective
    calc
      realPolynomialToComplex A =
          realPolynomialToComplex
            (Polynomial.C constant *
              (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
              (hA.rootProductData.interiorRealRootPairParameters.map fun s =>
                ((X : ℝ[X]) ^ 2 - Polynomial.C (s ^ 2)) ^ 2).prod *
              (hA.rootProductData.outsideRealRoots.map fun s =>
                Polynomial.C (s.value ^ 2) - (X : ℝ[X]) ^ 2).prod *
              (hA.rootProductData.imaginaryRootParameters.map fun r =>
                (X : ℝ[X]) ^ 2 + Polynomial.C (r ^ 2)).prod *
              (hA.rootProductData.complexRootParameters.map fun z =>
                (X : ℝ[X]) ^ 4 + Polynomial.C (2 * (z.2 ^ 2 - z.1 ^ 2)) * X ^ 2 +
                  Polynomial.C ((z.1 ^ 2 + z.2 ^ 2) ^ 2)).prod) := by
        exact hcomplex.trans hsource.symm
      _ =
          realPolynomialToComplex
            (Polynomial.C constant *
              (Polynomial.X : ℝ[X]) ^ (2 * hA.rootProductData.zeroRootPairs) *
              DegreeParityFactorCertificate.productPoly
                (hA.rootProductData.interiorRealRootPairParameters.map
                  DegreeParityFactorCertificate.interiorRealRootPair) *
              DegreeParityFactorCertificate.productPoly
                (hA.rootProductData.outsideRealRoots.map (fun s =>
                  DegreeParityFactorCertificate.realRoot s.value s.outside)) *
              DegreeParityFactorCertificate.productPoly
                (hA.rootProductData.imaginaryRootParameters.map
                  DegreeParityFactorCertificate.imaginaryRoot) *
              DegreeParityFactorCertificate.productPoly
                (hA.rootProductData.complexRootParameters.map (fun z =>
                  DegreeParityFactorCertificate.complexRoot z.1 z.2))) := by
        simp
  exact hA.factorizationOfProductEq constant constant_nonnegative hproduct

/-- The source-grouped complex product identity reduces the remaining Lemma 6
factorization to the certified source scalar sign [GSLW19,
BlockHam.tex:450-480]. -/
noncomputable def SourceHypotheses.factorizationOfSourceProduct
    {A : ℝ[X]} {k : ℕ} (hA : SourceHypotheses A k) :
    SourceRootClassFactorization A k :=
  hA.factorizationOfComplexProductEq hA.rootProductData.sourceConstant
    hA.sourceConstant_nonnegative hA.realPolynomialToComplex_eq_sourceProduct

/-- The source form multiplied by its conjugate gives the real interval-square
decomposition [GSLW19, BlockHam.tex:475-480]. -/
theorem intervalComplexForm_mul_conj (B C : ℝ[X]) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    intervalComplexForm B C x * starRingEnd ℂ (intervalComplexForm B C x) =
      (((B.eval x) ^ 2 + (1 - x ^ 2) * (C.eval x) ^ 2 : ℝ) : ℂ) := by
  have hs : ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ^ 2 =
      ((1 - x ^ 2 : ℝ) : ℂ) := by
    calc
      ((Real.sqrt (1 - x ^ 2) : ℝ) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 :=
        sq_sqrt_one_sub_sq (x := x) hx
      _ = ((1 - x ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
  have hcast : ((1 - x ^ 2 : ℝ) : ℂ) = 1 - (x : ℂ) ^ 2 := by
    push_cast
    ring
  simp [intervalComplexForm]
  ring_nf
  rw [hs, hcast, Complex.I_sq]
  ring_nf

/-- Evaluating an interval-square certificate gives the source's
`W(x) W(x)^* = A(x)` identity [GSLW19, BlockHam.tex:475-480]. -/
theorem intervalComplexForm_mul_conj_eq_of_certificate {A : ℝ[X]}
    (h : Certificate A) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    intervalComplexForm h.B h.C x *
        starRingEnd ℂ (intervalComplexForm h.B h.C x) =
      ((A.eval x : ℝ) : ℂ) := by
  let B : ℝ[X] := h.B
  let C : ℝ[X] := h.C
  have h_eq : A = B ^ 2 + (1 - X ^ 2) * C ^ 2 := by
    simpa [B, C] using h.eq_decomposition
  change intervalComplexForm B C x * starRingEnd ℂ (intervalComplexForm B C x) =
    ((A.eval x : ℝ) : ℂ)
  rw [intervalComplexForm_mul_conj B C hx]
  have heval :
      A.eval x = (B.eval x) ^ 2 + (1 - x ^ 2) * (C.eval x) ^ 2 := by
    rw [h_eq]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow]
  rw [heval]

end Complement.Interval

namespace Complement.Interval.Witness

/-- If `1 - P^2` has an interval-square certificate, then the real component
`P(x)` and the source form `B(x)+i sqrt(1-x^2) C(x)` satisfy the pointwise
unitarity normalization from [GSLW19, BlockHam.tex:475-480]. -/
theorem real_norm_plus_intervalComplexForm_norm_eq_one {P : ℝ[X]}
    (h : Complement.Interval.Certificate (1 - P ^ 2))
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (((P.eval x) ^ 2 : ℝ) : ℂ) +
        Complement.Interval.intervalComplexForm h.B h.C x *
          starRingEnd ℂ (Complement.Interval.intervalComplexForm h.B h.C x) =
      1 := by
  rw [Complement.Interval.intervalComplexForm_mul_conj_eq_of_certificate h hx]
  have heval : (1 - P ^ 2 : ℝ[X]).eval x = 1 - (P.eval x) ^ 2 := by
    simp [Polynomial.eval_sub, Polynomial.eval_pow]
  rw [heval]
  norm_num

end Complement.Interval.Witness

namespace Complement.Interval

/-- Compatibility name for the staged interval witness theorem. -/
theorem real_norm_plus_intervalComplexForm_norm_eq_one {P : ℝ[X]}
    (h : Certificate (1 - P ^ 2)) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (((P.eval x) ^ 2 : ℝ) : ℂ) +
        intervalComplexForm h.B h.C x *
          starRingEnd ℂ (intervalComplexForm h.B h.C x) =
      1 :=
  Complement.Interval.Witness.real_norm_plus_intervalComplexForm_norm_eq_one h hx

end Complement.Interval

end QuantumAlg
