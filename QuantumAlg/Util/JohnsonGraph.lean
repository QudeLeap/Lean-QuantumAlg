/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.Matrix.SymmetricStochastic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Finset.Basic
public import Mathlib.Combinatorics.Colex

/-!
# Johnson Graph — Definition and basic properties

The Johnson graph J(N,r) has vertices given by all r-element subsets
of [N] = {0, ..., N-1}. Two vertices R,R' are adjacent when
|R ∩ R'| = r-1, i.e., they differ by exactly one element.

[dW19, qcnotes.tex:3342-3377]
-/

@[expose] public section

namespace QuantumAlg

open Finset
open scoped BigOperators

/-! ### Vertex type and adjacency -/

/-- A vertex of J(N,r): an r-element subset of Fin N. -/
def JohnsonVertex (N r : ℕ) := { s : Finset (Fin N) // s.card = r }

instance (N r : ℕ) : Fintype (JohnsonVertex N r) :=
  Fintype.subtype (Finset.filter (fun s => s.card = r) Finset.univ) (by simp)

namespace JohnsonVertex

variable {N r : ℕ}

/-- Two vertices are adjacent when their intersection has size r-1.
Requires `0 < r` so that `r-1` is meaningful. -/
def isAdjacent (R R' : JohnsonVertex N r) : Prop :=
  (R.val ∩ R'.val).card = r - 1

instance (N r : ℕ) : DecidableEq (JohnsonVertex N r) :=
  Subtype.instDecidableEq

/-- The degree (number of neighbours) of any vertex in J(N,r).
Requires `r < N` to ensure degree > 0. -/
def degree (N r : ℕ) : ℕ := r * (N - r)

/-- Vertices adjacent to R form a Finset. -/
def neighbors (R : JohnsonVertex N r) : Finset (JohnsonVertex N r) :=
  (Finset.univ : Finset (JohnsonVertex N r)).filter (fun R' =>
    (R.val ∩ R'.val).card = r - 1)

/-- Symmetry: if R is adjacent to R', then R' is adjacent to R. -/
lemma isAdjacent_symm {R R' : JohnsonVertex N r} (h : isAdjacent R R') : isAdjacent R' R := by
  dsimp [isAdjacent] at h ⊢
  rw [Finset.inter_comm R'.val R.val]
  exact h

/-- Non-degeneracy: r > 0 ensures degree > 0 when r < N. -/
lemma degree_pos (hr_pos : 0 < r) (hr_lt_N : r < N) : 0 < degree N r := by
  rw [degree]
  have hN_sub_r_pos : 0 < N - r := Nat.sub_pos_of_lt hr_lt_N
  exact mul_pos hr_pos hN_sub_r_pos

/-! ### Swap operation -/

/-- The "swap set" R' = (R \ {x}) ∪ {y} has cardinality r if x ∈ R and y ∉ R. -/
def swapSet (R : JohnsonVertex N r) (x : Fin N) (hx : x ∈ R.val) (y : Fin N)
    (hy : y ∉ R.val) : JohnsonVertex N r :=
  ⟨(R.val.erase x) ∪ {y}, by
    have h_disjoint : Disjoint (R.val.erase x) {y} :=
      Finset.disjoint_singleton_right.mpr (by simp [hy])
    have hr_pos : 1 ≤ r := by
      have hpos : 0 < R.val.card := Finset.card_pos.mpr ⟨x, hx⟩
      rw [R.property] at hpos
      omega
    rw [Finset.card_union_of_disjoint h_disjoint,
      Finset.card_singleton,
      Finset.card_erase_of_mem hx, R.property]
    exact Nat.sub_add_cancel hr_pos⟩

/-- The swap-set is adjacent to R: |R ∩ R'| = r-1. -/
lemma isAdjacent_swapSet (R : JohnsonVertex N r) (x : Fin N) (hx : x ∈ R.val) (y : Fin N)
    (hy : y ∉ R.val) : isAdjacent R (swapSet R x hx y hy) := by
  dsimp [isAdjacent, swapSet]
  have h_inter_eq : R.val ∩ ((R.val.erase x) ∪ {y}) = R.val.erase x := by
    rw [Finset.inter_union_distrib_left]
    have h1 : R.val ∩ (R.val.erase x) = R.val.erase x :=
      Finset.inter_eq_right.mpr (Finset.erase_subset x R.val)
    have h2 : R.val ∩ {y} = ∅ := by simp [hy]
    rw [h1, h2, Finset.union_empty]
  rw [h_inter_eq, Finset.card_erase_of_mem hx, R.property]

/-! ### Neighbor cardinality infrastructure

Building blocks for proving `|neighbors R| = r * (N - r)` via an explicit bijection
between the neighbor set and the product `{x ∈ R.val} × {y ∉ R.val}`. -/

/-- For a neighbor R' of R, the set difference R \ R' has size 1. -/
lemma card_sdiff_eq_one {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R') (hr_pos : 0 < r) :
    (R.val \ R'.val).card = 1 := by
  dsimp [isAdjacent] at h_adj
  have h_eq : (R.val \ R'.val).card + (R.val ∩ R'.val).card = R.val.card :=
    Finset.card_sdiff_add_card_inter R.val R'.val
  rw [h_adj, R.property] at h_eq
  omega

/-- For a neighbor R' of R, extract the unique element x ∈ R \ R'. -/
noncomputable def uniqueRemoved {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R')
    (hr_pos : 0 < r) : Fin N :=
  Classical.choose (Finset.card_eq_one.mp (card_sdiff_eq_one h_adj hr_pos))

lemma uniqueRemoved_mem {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R')
    (hr_pos : 0 < r) : uniqueRemoved h_adj hr_pos ∈ R.val ∧
    uniqueRemoved h_adj hr_pos ∉ R'.val := by
  have hcard : (R.val \ R'.val).card = 1 := card_sdiff_eq_one h_adj hr_pos
  have hspec : R.val \ R'.val = {uniqueRemoved h_adj hr_pos} :=
    Classical.choose_spec (Finset.card_eq_one.mp hcard)
  have h_mem : uniqueRemoved h_adj hr_pos ∈ R.val \ R'.val := by
    rw [hspec]
    exact Finset.mem_singleton.mpr rfl
  exact Finset.mem_sdiff.mp h_mem

/-- For a neighbor R' of R, extract the unique element y ∈ R' \ R. -/
noncomputable def uniqueAdded {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R')
    (hr_pos : 0 < r) : Fin N :=
  Classical.choose (Finset.card_eq_one.mp (card_sdiff_eq_one (isAdjacent_symm h_adj) hr_pos))

lemma uniqueAdded_mem {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R')
    (hr_pos : 0 < r) : uniqueAdded h_adj hr_pos ∉ R.val ∧
    uniqueAdded h_adj hr_pos ∈ R'.val := by
  have hcard : (R'.val \ R.val).card = 1 := card_sdiff_eq_one (isAdjacent_symm h_adj) hr_pos
  have hspec : R'.val \ R.val = {uniqueAdded h_adj hr_pos} :=
    Classical.choose_spec (Finset.card_eq_one.mp hcard)
  have h_mem : uniqueAdded h_adj hr_pos ∈ R'.val \ R.val := by
    rw [hspec]
    exact Finset.mem_singleton.mpr rfl
  rcases Finset.mem_sdiff.mp h_mem with ⟨h1, h2⟩
  exact ⟨h2, h1⟩

/-! ### Finset identities for swapSet -/

lemma sdiff_swapSet_eq_singleton (R : JohnsonVertex N r) (x : Fin N) (hx : x ∈ R.val)
    (y : Fin N) (hy : y ∉ R.val) : R.val \ (swapSet R x hx y hy).val = {x} := by
  dsimp [swapSet]
  ext a
  constructor
  · intro ha
    rw [Finset.mem_sdiff] at ha
    rcases ha with ⟨haR, ha_not⟩
    rw [Finset.mem_singleton]
    by_contra hne
    -- hne: a ≠ x, so a ∈ R.val.erase x
    have ha_erase : a ∈ R.val.erase x := by
      rw [Finset.mem_erase]
      exact ⟨hne, haR⟩
    have ha_union : a ∈ (R.val.erase x) ∪ {y} := Finset.mem_union_left _ ha_erase
    exact ha_not ha_union
  · intro ha
    rw [Finset.mem_singleton] at ha; subst a
    rw [Finset.mem_sdiff]
    constructor
    · exact hx
    · have hxy : x ≠ y := by intro heq; subst heq; exact hy hx
      simp [hx, hxy]

lemma swapSet_sdiff_eq_singleton (R : JohnsonVertex N r) (x : Fin N) (hx : x ∈ R.val)
    (y : Fin N) (hy : y ∉ R.val) : (swapSet R x hx y hy).val \ R.val = {y} := by
  dsimp [swapSet]
  ext a
  constructor
  · intro ha
    rw [Finset.mem_sdiff] at ha
    rcases ha with ⟨ha_union, ha_notR⟩
    rw [Finset.mem_union] at ha_union
    rcases ha_union with (ha_erase | ha_sing)
    · rw [Finset.mem_erase] at ha_erase
      rcases ha_erase with ⟨_, haR⟩
      exact absurd haR ha_notR
    · rw [Finset.mem_singleton] at ha_sing
      rw [Finset.mem_singleton]; exact ha_sing
  · intro ha
    rw [Finset.mem_singleton] at ha; subst a
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_union]
      right; exact Finset.mem_singleton.mpr rfl
    · exact hy

/-- Reconstruct R' from R and the unique elements x ∈ R \ R', y ∈ R' \ R. -/
lemma swapSet_reconstruct {R R' : JohnsonVertex N r} (h_adj : isAdjacent R R') (hr_pos : 0 < r) :
    swapSet R (uniqueRemoved h_adj hr_pos) (uniqueRemoved_mem h_adj hr_pos).1
      (uniqueAdded h_adj hr_pos) (uniqueAdded_mem h_adj hr_pos).1 = R' := by
  set x := uniqueRemoved h_adj hr_pos
  set y := uniqueAdded h_adj hr_pos
  have hx_mem : x ∈ R.val := (uniqueRemoved_mem h_adj hr_pos).1
  have hx_not : x ∉ R'.val := (uniqueRemoved_mem h_adj hr_pos).2
  have hy_not : y ∉ R.val := (uniqueAdded_mem h_adj hr_pos).1
  have hy_mem : y ∈ R'.val := (uniqueAdded_mem h_adj hr_pos).2
  have h_sdiff_R : R.val \ R'.val = {x} :=
    Classical.choose_spec (Finset.card_eq_one.mp (card_sdiff_eq_one h_adj hr_pos))
  have h_sdiff_R' : R'.val \ R.val = {y} :=
    Classical.choose_spec (Finset.card_eq_one.mp (card_sdiff_eq_one (isAdjacent_symm h_adj) hr_pos))
  apply Subtype.ext; dsimp [swapSet]
  ext a
  constructor
  · intro ha
    rw [Finset.mem_union, Finset.mem_singleton] at ha
    rcases ha with (ha_erase | rfl)
    · -- a ∈ R.val.erase x, so a ≠ x and a ∈ R.val
      rw [Finset.mem_erase] at ha_erase
      rcases ha_erase with ⟨hne, haR⟩
      -- Since x is the only element of R \ R', and a ≠ x, we have a ∈ R'
      by_contra ha_not_R'
      have ha_sdiff : a ∈ R.val \ R'.val := Finset.mem_sdiff.mpr ⟨haR, ha_not_R'⟩
      rw [h_sdiff_R] at ha_sdiff
      rw [Finset.mem_singleton] at ha_sdiff
      exact hne ha_sdiff
    · exact hy_mem
  · intro haR'
    by_cases ha_eq_y : a = y
    · subst a; rw [Finset.mem_union]
      right; exact Finset.mem_singleton.mpr rfl
    · -- a ≠ y, and a ∈ R'.val. Since y is the only element in R' \ R, a must be in R.val
      have ha_not_R'_sdiff : a ∉ R'.val \ R.val := by
        intro h; rw [h_sdiff_R'] at h
        rw [Finset.mem_singleton] at h; exact ha_eq_y h
      have haR : a ∈ R.val := by
        by_contra ha_not_R
        exact ha_not_R'_sdiff (Finset.mem_sdiff.mpr ⟨haR', ha_not_R⟩)
      have ha_ne_x : a ≠ x := by
        intro heq; subst a; exact hx_not haR'
      rw [Finset.mem_union]
      left; rw [Finset.mem_erase]
      exact ⟨ha_ne_x, haR⟩

instance (R : JohnsonVertex N r) : DecidablePred (isAdjacent R) :=
  inferInstanceAs (DecidablePred (fun (R' : JohnsonVertex N r) => (R.val ∩ R'.val).card = r - 1))

instance (R : JohnsonVertex N r) : Fintype {R' : JohnsonVertex N r // isAdjacent R R'} :=
  inferInstanceAs (Fintype {R' : JohnsonVertex N r // (R.val ∩ R'.val).card = r - 1})

/-- The bijection between neighbor choices and the neighbor set.
`{x ∈ R.val} × {y ∉ R.val} ≃ {R' | isAdjacent R R'}`. -/
noncomputable def NeighborEquiv (R : JohnsonVertex N r) (hr_pos : 0 < r) :
    ({x : Fin N // x ∈ R.val} × {y : Fin N // y ∉ R.val}) ≃
    {R' : JohnsonVertex N r // isAdjacent R R'} where
  toFun := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ =>
    ⟨swapSet R x hx y hy, isAdjacent_swapSet R x hx y hy⟩
  invFun := fun ⟨R', h_adj⟩ =>
    let xr := uniqueRemoved h_adj hr_pos
    let yr := uniqueAdded h_adj hr_pos
    (⟨xr, (uniqueRemoved_mem h_adj hr_pos).1⟩,
     ⟨yr, (uniqueAdded_mem h_adj hr_pos).1⟩)
  left_inv := by
    intro p; rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hx' : uniqueRemoved (isAdjacent_swapSet R x hx y hy) hr_pos = x := by
      have hmem : uniqueRemoved (isAdjacent_swapSet R x hx y hy) hr_pos ∈
          R.val \ (swapSet R x hx y hy).val :=
        Finset.mem_sdiff.mpr ⟨(uniqueRemoved_mem (isAdjacent_swapSet R x hx y hy) hr_pos).1,
          (uniqueRemoved_mem (isAdjacent_swapSet R x hx y hy) hr_pos).2⟩
      have h_eq : R.val \ (swapSet R x hx y hy).val = {x} :=
        sdiff_swapSet_eq_singleton R x hx y hy
      rw [h_eq] at hmem
      exact Finset.mem_singleton.mp hmem
    have hy' : uniqueAdded (isAdjacent_swapSet R x hx y hy) hr_pos = y := by
      have hmem : uniqueAdded (isAdjacent_swapSet R x hx y hy) hr_pos ∈
          (swapSet R x hx y hy).val \ R.val :=
        Finset.mem_sdiff.mpr ⟨(uniqueAdded_mem (isAdjacent_swapSet R x hx y hy) hr_pos).2,
          (uniqueAdded_mem (isAdjacent_swapSet R x hx y hy) hr_pos).1⟩
      have h_eq : (swapSet R x hx y hy).val \ R.val = {y} :=
        swapSet_sdiff_eq_singleton R x hx y hy
      rw [h_eq] at hmem
      exact Finset.mem_singleton.mp hmem
    ext <;> simp [hx', hy']
  right_inv := by
    intro p; rcases p with ⟨R', h_adj⟩
    apply Subtype.ext
    exact swapSet_reconstruct h_adj hr_pos

/-- **Degree theorem**: every vertex in J(N,r) has exactly r*(N-r) neighbours. -/
lemma neighbors_card (hr_pos : 0 < r) (_hr_lt_N : r < N) (R : JohnsonVertex N r) :
    (neighbors R).card = degree N r := by
  rw [degree]
  -- From the bijection, |neighbors R| = r * (N - r)
  have h_equiv := Fintype.card_congr (NeighborEquiv R hr_pos)
  -- h_equiv: |{x ∈ R.val} × {y ∉ R.val}| = |{R' // isAdjacent R R'}|
  rw [Fintype.card_prod] at h_equiv
  -- h_equiv: |InSet| * |OutSet| = |target|
  have h_card_in : Fintype.card {x : Fin N // x ∈ R.val} = r := by
    simp [R.property]
  have h_card_out : Fintype.card {y : Fin N // y ∉ R.val} = N - r := by
    -- |univ| = N, |R.val| = r, so |complement| = N - r
    have h_total : Fintype.card (Fin N) = N := Fintype.card_fin N
    calc
      Fintype.card {y : Fin N // y ∉ R.val}
          = Fintype.card (Fin N) - Fintype.card {y : Fin N // y ∈ R.val} := by
        apply Fintype.card_subtype_compl
      _ = N - r := by simp [R.property, h_total]
  have h_card_target : Fintype.card {R' : JohnsonVertex N r // isAdjacent R R'} = (neighbors
    R).card := by
    rw [neighbors]
    -- Fintype.card_subtype: Fintype.card {R' // P R'} = (Finset.filter P Finset.univ).card
    exact Fintype.card_subtype _
  rw [h_card_in, h_card_out, h_card_target] at h_equiv
  -- h_equiv: r * (N - r) = (neighbors R).card
  exact h_equiv.symm

/-! ### Bitmask embedding

An r-subset of `Fin N` is encoded by its bitmask in `Fin (2 ^ N)`.
Unused bitmasks receive identity self-loops in the padded matrix. -/

/-! ### Geometric series helper -/

private lemma sum_range_two_pow_eq_sub_one (N : ℕ) : ∑ j ∈ Finset.range N, (2 : ℕ) ^ j = 2 ^ N - 1
  := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 1 ≤ 2 ^ N := Nat.one_le_two_pow
      omega

/-- The bitmask embedding of a Johnson vertex: Σ_{i ∈ R} 2^i ∈ [0, 2^N).
Since `2^N > C(N,r)` for all r, this gives an injection into `Fin (2 ^ N)`. -/
noncomputable def embed (R : JohnsonVertex N r) : Fin (2 ^ N) :=
  -- Represent R.val as a bitmask: sum of 2^i for i ∈ R.val
  let bits : ℕ := (R.val).sum (fun i => 2 ^ (i.val : ℕ))
  have h_bound : bits < 2 ^ N := by
    dsimp [bits]
    calc
      (R.val).sum (fun i => 2 ^ (i.val : ℕ))
          ≤ (Finset.univ : Finset (Fin N)).sum (fun i => 2 ^ (i.val : ℕ)) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = ∑ j ∈ Finset.range N, (2 : ℕ) ^ j := by
        simp [Fin.sum_univ_eq_sum_range]
      _ = (2 : ℕ) ^ N - 1 := sum_range_two_pow_eq_sub_one N
      _ < 2 ^ N := by
        have hpos : 0 < (2 : ℕ) ^ N := pow_pos (by norm_num) N
        omega
  Fin.mk bits h_bound

/-! ### Binary representation uniqueness for sums of distinct powers of two -/

lemma embed_injective : Function.Injective (embed (N := N) (r := r)) := by
  intro R₁ R₂ h
  apply_fun Fin.val at h
  dsimp [embed] at h
  apply Subtype.ext
  -- h: sum over R₁.val = sum over R₂.val of 2^(i.val)
  -- Convert to Finset ℕ images: the sums over images are equal
  have himg_sum_eq : (∑ v ∈ (Finset.image Fin.val (R₁.val : Finset (Fin N))), (2 : ℕ) ^ v) =
                    (∑ v ∈ (Finset.image Fin.val (R₂.val : Finset (Fin N))), (2 : ℕ) ^ v) := by
    calc
      ∑ v ∈ (Finset.image Fin.val (R₁.val : Finset (Fin N))), (2 : ℕ) ^ v
          = ∑ i ∈ (R₁.val : Finset (Fin N)), (2 : ℕ) ^ (i.val : ℕ) := by
        rw [Finset.sum_image (fun x _ y _ hxy => Fin.ext hxy)]
      _ = ∑ i ∈ (R₂.val : Finset (Fin N)), (2 : ℕ) ^ (i.val : ℕ) := by rw [h]
      _ = ∑ v ∈ (Finset.image Fin.val (R₂.val : Finset (Fin N))), (2 : ℕ) ^ v := by
        rw [Finset.sum_image (fun x _ y _ hxy => Fin.ext hxy)]
  -- Finset.geomSum_injective: equal sums of powers of 2 → Finsets equal
  have himg_eq : Finset.image Fin.val R₁.val = Finset.image Fin.val R₂.val :=
    (Finset.geomSum_injective (by norm_num : 2 ≤ (2 : ℕ))).eq_iff.mp himg_sum_eq
  -- Fin.val is injective, so image equality → original Finsets equal
  exact Finset.image_injective Fin.val_injective himg_eq

/-- The active set: all embedded Johnson vertices as bitmasks in `Fin (2 ^ N)`. -/
noncomputable def activeSet : Finset (Fin (2 ^ N)) :=
  (Finset.univ : Finset (JohnsonVertex N r)).image embed

/-- The active set has exactly `C(N,r)` elements (embedding is injective). -/
lemma activeSet_card : (activeSet (N := N) (r := r)).card = (Finset.univ : Finset (JohnsonVertex
  N r)).card := by
  rw [activeSet]
  exact Finset.card_image_of_injective _ embed_injective

/-! ### Padding: Option decoder -/

/-- Existence proof shared by `decodeOpt` and `decodeOpt_embed`.
Given `i ∈ activeSet`, produces `∃ R, embed R = i`. -/
lemma existsEmbed (N r : ℕ) (i : Fin (2 ^ N))
    (h : i ∈ activeSet (N := N) (r := r)) : ∃ (R : JohnsonVertex N r), embed R = i := by
  unfold activeSet at h
  rcases Finset.mem_image.mp h with ⟨R, _, hR⟩
  exact ⟨R, hR⟩

/-- Decode `Fin (2 ^ N)` to `Option (JohnsonVertex N r)`. Active→some R, padding→none.
Takes explicit `N r` to avoid metavariables from section variable shadowing. -/
noncomputable def decodeOpt (N r : ℕ) (i : Fin (2 ^ N)) : Option (JohnsonVertex N r) :=
  if h : i ∈ activeSet (N := N) (r := r) then
    some (Classical.choose (existsEmbed N r i h))
  else none

lemma decodeOpt_embed (R : JohnsonVertex N r) : decodeOpt N r (embed R) = some R := by
  rw [decodeOpt]
  have h_mem : embed R ∈ activeSet (N := N) (r := r) := by
    rw [activeSet]; exact Finset.mem_image.mpr ⟨R, Finset.mem_univ _, rfl⟩
  rw [dif_pos h_mem]
  congr 1
  apply embed_injective
  -- Goal: embed (Classical.choose (existsEmbed N r (embed R) h_mem)) = embed R
  -- Classical.choose_spec gives exactly this
  exact Classical.choose_spec (existsEmbed N r (embed R) h_mem)

/-! ### Padded Transition Matrix (dite + Option.get) -/

/-- Padded matrix entry using nested match (avoids equation compiler metavariables
from simultaneous matching). Takes explicit `N r` to prevent metavariables
from section variables. -/
noncomputable def padEntry (N r : ℕ) (i j : Fin (2 ^ N)) : ℝ :=
  match decodeOpt (N := N) (r := r) i with
  | none =>
    match decodeOpt (N := N) (r := r) j with
    | none => if i = j then (1 : ℝ) else 0
    | some _ => 0
  | some R =>
    match decodeOpt (N := N) (r := r) j with
    | none => 0
    | some R' => if isAdjacent R R' then (1 : ℝ) / (degree N r : ℝ) else 0

/-- The padded TransitionMatrix. Requires `0 < r < N`. -/
noncomputable def transitionMatrix (hr_pos : 0 < r) (hr_lt_N : r < N) : Matrix.SymmetricStochastic
  (Fin (2 ^ N)) where
  mat i j := padEntry N r i j
  symmetric := by
    unfold Matrix.IsSymm
    ext i j
    change padEntry N r j i = padEntry N r i j
    unfold padEntry
    cases h_i : decodeOpt (N := N) (r := r) i
    · -- decodeOpt i = none
      cases h_j : decodeOpt (N := N) (r := r) j
      · -- none, none: (if j = i then 1 else 0) = (if i = j then 1 else 0)
        by_cases h_eq : i = j
        · simp [h_eq]
        · simp [h_eq, Ne.symm h_eq]
      · -- none, some R': 0 = 0
        rfl
    · -- decodeOpt i = some R
      rename_i R
      simp only [one_div]
      cases h_j : decodeOpt (N := N) (r := r) j
      · -- some R, none: 0 = 0
        rfl
      · -- some R, some R'
        rename_i R'
        by_cases h_adj : isAdjacent R R'
        · have h_adj_symm := isAdjacent_symm h_adj
          simp [h_adj, h_adj_symm]
        · have h_adj_symm : ¬ isAdjacent R' R := by
            intro h; exact h_adj (isAdjacent_symm h)
          simp [h_adj, h_adj_symm]
  nonneg := by
    intro i j
    unfold padEntry
    have h_deg_pos : 0 < (degree N r : ℝ) := by exact_mod_cast degree_pos hr_pos hr_lt_N
    cases h_i : decodeOpt (N := N) (r := r) i
    · -- decodeOpt i = none
      cases h_j : decodeOpt (N := N) (r := r) j
      · -- none, none: if i = j then 1 else 0
        split_ifs <;> positivity
      · -- none, some R': 0
        positivity
    · -- decodeOpt i = some R
      rename_i R
      cases h_j : decodeOpt (N := N) (r := r) j
      · -- some R, none: 0
        positivity
      · -- some R, some R': if isAdjacent R R' then 1/d else 0
        rename_i R'
        simp only [one_div, ge_iff_le]
        split_ifs
        · -- 1 / (degree N r : ℝ) ≥ 0
          positivity
        · -- 0 ≥ 0
          positivity
  rowSum_one := by
    intro i
    unfold padEntry
    cases h_i : decodeOpt (N := N) (r := r) i
    case none =>
      -- Goal: ∑ y, (match decodeOpt y with none => if i=y then 1 else 0 | some _ => 0) = 1
      have h_term : ∀ y, (match decodeOpt (N := N) (r := r) y with
          | none => if i = y then (1 : ℝ) else 0
          | some _ => (0 : ℝ)) = if i = y then (1 : ℝ) else 0 := by
        intro y
        cases h_y : decodeOpt (N := N) (r := r) y
        · simp
        · rename_i val
          have hy_ne_i : y ≠ i := by
            intro h_eq; subst h_eq; rw [h_i] at h_y; simp at h_y
          simp [hy_ne_i.symm]
      simp [h_term]
    case some R =>
      -- Goal: ∑ y, (match decodeOpt y with none => 0 | some R' => if isAdjacent R R' then 1/d
      -- else 0) = 1
      have hemb : embed R = i := by
        by_cases hmem : i ∈ activeSet (N := N) (r := r)
        · let h_exists := existsEmbed N r i hmem
          have h_decode : decodeOpt N r i = some (Classical.choose h_exists) := by
            rw [decodeOpt, dif_pos hmem]
          rw [h_decode] at h_i
          have hR_eq := Option.some_inj.mp h_i
          -- hR_eq: R = Classical.choose h_exists
          have h_emb := Classical.choose_spec h_exists
          -- h_emb: embed (Classical.choose h_exists) = i
          rw [hR_eq] at h_emb
          exact h_emb
        · rw [decodeOpt, dif_neg hmem] at h_i
          simp at h_i
      -- Active-vertex summand: 1/d for neighbours, 0 otherwise
      let f (y : Fin (2 ^ N)) : ℝ :=
        match decodeOpt (N := N) (r := r) y with
        | none => (0 : ℝ)
        | some R' => if isAdjacent R R' then (1 : ℝ) / (degree N r : ℝ) else (0 : ℝ)
      have h_sum_eq : (∑ y : Fin (2 ^ N), f y) = 1 := by
        have h_subset : (∑ y : Fin (2 ^ N), f y) =
            (∑ y ∈ activeSet (N := N) (r := r), f y) := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro y _ hy
          dsimp [f]
          have hy_none : decodeOpt (N := N) (r := r) y = none := by
            unfold decodeOpt; simp [hy]
          simp [hy_none]
        rw [h_subset]
        rw [activeSet, Finset.sum_image (fun x _ y _ h => embed_injective h)]
        -- Goal: ∑ R' : JohnsonVertex N r, f (embed R') = 1
        have h_inner : ∀ R' : JohnsonVertex N r, f (embed R') =
            if isAdjacent R R' then (1 : ℝ) / (degree N r : ℝ) else 0 := by
          intro R'
          dsimp [f]
          simp [decodeOpt_embed R']
        rw [Finset.sum_congr rfl (fun R' _ => h_inner R')]
        -- Split sum over isAdjacent predicate → sum over neighbors
        rw [← Finset.sum_filter,
          show (Finset.univ : Finset (JohnsonVertex N r)).filter (isAdjacent R) = neighbors R
            from by ext R'; simp [neighbors, isAdjacent]]
        -- Sum constant over neighbors → card * (1/d)
        rw [Finset.sum_const, nsmul_eq_mul]
        -- Degree theorem: |neighbors R| = d → d * (1/d) = 1
        rw [neighbors_card hr_pos hr_lt_N R]
        have h_deg_ne_zero : (degree N r : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (ne_of_gt (degree_pos hr_pos hr_lt_N))
        field_simp [h_deg_ne_zero]
      simpa [f] using h_sum_eq

/-! ### Active-subspace bridge lemmas

The padded matrix is block-diagonal:
- **Active×Active** block: Johnson graph walk matrix (1/degree for adjacent vertices)
- **Padding×Padding** block: Identity matrix (self-loops)
- **Cross blocks**: Zero

These lemmas establish the structural foundation for connecting the padded
`TransitionMatrix` to the quantum walk framework without silently conflating
the full `2^N`-dimensional space with the active `C(N,r)`-dimensional subspace. -/

/-- `decodeOpt i = none` iff `i` is not in the active set (i.e., is a padding vertex). -/
lemma decodeOpt_eq_none_iff (i : Fin (2 ^ N)) :
    decodeOpt N r i = none ↔ i ∉ activeSet (N := N) (r := r) := by
  constructor
  · intro h hmem
    rw [decodeOpt, dif_pos hmem] at h
    simp at h
  · intro h
    rw [decodeOpt, dif_neg h]

/-- Converse of `decodeOpt_embed`: if `decodeOpt` returns `some R`, then `embed R = i`.
Together with `decodeOpt_embed`, this gives a bijection between the active set
and `JohnsonVertex N r`. -/
lemma embed_of_decodeOpt_eq_some {i : Fin (2 ^ N)} {R : JohnsonVertex N r}
    (h : decodeOpt N r i = some R) : embed R = i := by
  by_cases hmem : i ∈ activeSet (N := N) (r := r)
  · let h_exists := existsEmbed N r i hmem
    have h_decode : decodeOpt N r i = some (Classical.choose h_exists) := by
      rw [decodeOpt, dif_pos hmem]
    rw [h_decode] at h
    have hR_eq := Option.some_inj.mp h
    -- hR_eq: R = Classical.choose h_exists
    have h_emb := Classical.choose_spec h_exists
    -- h_emb: embed (Classical.choose h_exists) = i
    rw [hR_eq] at h_emb
    exact h_emb
  · rw [decodeOpt, dif_neg hmem] at h
    simp at h

/-- Padding-padding entry: the self-loop identity block. -/
lemma padEntry_none_none (i j : Fin (2 ^ N))
    (h_i : decodeOpt N r i = none) (h_j : decodeOpt N r j = none) :
    padEntry N r i j = if i = j then (1 : ℝ) else 0 := by
  unfold padEntry; simp [h_i, h_j]

/-- Active-padding entry: cross terms are always zero. -/
lemma padEntry_some_none (i j : Fin (2 ^ N)) (R : JohnsonVertex N r)
    (h_i : decodeOpt N r i = some R) (h_j : decodeOpt N r j = none) :
    padEntry N r i j = 0 := by
  unfold padEntry; simp [h_i, h_j]

/-- Padding-active entry: cross terms are always zero. -/
lemma padEntry_none_some (i j : Fin (2 ^ N)) (R : JohnsonVertex N r)
    (h_i : decodeOpt N r i = none) (h_j : decodeOpt N r j = some R) :
    padEntry N r i j = 0 := by
  unfold padEntry; simp [h_i, h_j]

/-- Active-active entry via `embed`: recovers the Johnson graph walk matrix.
Equivalent to `1/degree` for adjacent vertices, `0` otherwise. -/
lemma padEntry_embed_embed (R R' : JohnsonVertex N r) :
    padEntry N r (embed R) (embed R') =
    if isAdjacent R R' then (1 : ℝ) / (degree N r : ℝ) else 0 := by
  unfold padEntry; simp [decodeOpt_embed]

/-- Cross terms between active and padding subspaces are always zero.
This establishes the block-diagonal structure of the padded matrix. -/
lemma padEntry_active_padding_zero (i j : Fin (2 ^ N)) (R : JohnsonVertex N r)
    (h_i : decodeOpt N r i = some R) (h_j : decodeOpt N r j = none) :
    padEntry N r i j = 0 ∧ padEntry N r j i = 0 := by
  constructor
  · exact padEntry_some_none i j R h_i h_j
  · exact padEntry_none_some j i R h_j h_i

/-- For an active vertex, the sum over all indices equals the sum over `activeSet`.
Padding terms contribute zero, so the sum naturally restricts to the active subspace. -/
lemma sum_padEntry_active_eq_sum_over_activeSet
    (i : Fin (2 ^ N)) (R : JohnsonVertex N r) (h_i : decodeOpt N r i = some R) :
    (∑ j : Fin (2 ^ N), padEntry N r i j) =
    (∑ j ∈ activeSet (N := N) (r := r), padEntry N r i j) := by
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro j _ hj
  have h_j : decodeOpt N r j = none := by
    rwa [decodeOpt_eq_none_iff]
  exact padEntry_some_none i j R h_i h_j

/-! ### Marked fraction separation

We keep two distinct definitions to avoid silently identifying the native
Johnson-graph marked fraction with the diluted (padded) marked fraction.
The quantum-walk analysis must use the Johnson-native fraction for the
complexity formula; the padded fraction is only what the hardware "sees". -/

/-- Native Johnson-graph marked fraction: `|M| / C(N,r)`.
This is the marked fraction used in complexity formulas (not diluted by padding). -/
noncomputable def johnsonMarkedFraction (marked : Finset (JohnsonVertex N r)) : ℝ :=
  (marked.card : ℝ) / (Finset.card (Finset.univ : Finset (JohnsonVertex N r)) : ℝ)

/-- Physical (padded) marked fraction: `|M| / 2^N`.
This is what the quantum hardware sees. Always ≤ `johnsonMarkedFraction`
because `C(N,r) ≤ 2^N`. -/
noncomputable def paddedMarkedFraction (marked : Finset (JohnsonVertex N r)) : ℝ :=
  (marked.card : ℝ) / ((2 : ℝ) ^ N)

/-- The padded marked fraction is bounded above by the Johnson-native fraction
whenever `0 < r < N` (so that `JohnsonVertex N r` is nonempty and `C(N,r) ≤ 2^N`). -/
lemma paddedMarkedFraction_le_johnsonMarkedFraction (_hr_pos : 0 < r) (hr_lt_N : r < N)
    (marked : Finset (JohnsonVertex N r)) :
    paddedMarkedFraction marked ≤ johnsonMarkedFraction marked := by
  unfold paddedMarkedFraction johnsonMarkedFraction
  have h_marked_nonneg : 0 ≤ (marked.card : ℝ) := by exact_mod_cast Nat.zero_le _
  -- C(N,r) ≤ 2^N as natural numbers
  have h_card_le_nat : Finset.card (Finset.univ : Finset (JohnsonVertex N r)) ≤ 2 ^ N := by
    have h_fintype : Fintype.card (JohnsonVertex N r) ≤ 2 ^ N :=
      calc
        Fintype.card (JohnsonVertex N r) ≤ Fintype.card (Finset (Fin N)) :=
          Fintype.card_subtype_le _
        _ = 2 ^ N := by simp
    have h_card_eq : Fintype.card (JohnsonVertex N r) =
        Finset.card (Finset.univ : Finset (JohnsonVertex N r)) := by simp
    rw [← h_card_eq]
    exact h_fintype
  -- C(N,r) > 0 when 0 < r < N (construct an explicit r-subset: the first r elements)
  have h_nonempty : Nonempty (JohnsonVertex N r) := by
    -- Inject Fin r → Fin N via the identity on values (i.val < r < N)
    let f : Fin r → Fin N := fun i => ⟨i.val, Nat.lt_trans i.is_lt hr_lt_N⟩
    have h_inj : Function.Injective f := by
      intro a b h
      apply Fin.ext
      have h_val : (f a).val = (f b).val := congrArg Fin.val h
      simpa [f] using h_val
    let elems := Finset.image f Finset.univ
    have h_card : elems.card = r := by
      rw [Finset.card_image_of_injective _ h_inj]
      simp
    exact ⟨⟨elems, h_card⟩⟩
  have h_nonempty_finset : Finset.Nonempty (Finset.univ : Finset (JohnsonVertex N r)) := by
    rcases h_nonempty with ⟨v⟩
    exact ⟨v, Finset.mem_univ _⟩
  have h_card_pos_nat : 0 < Finset.card (Finset.univ : Finset (JohnsonVertex N r)) :=
    Finset.card_pos.mpr h_nonempty_finset
  have h_card_pos : 0 < (Finset.card (Finset.univ : Finset (JohnsonVertex N r)) : ℝ) := by
    exact_mod_cast h_card_pos_nat
  have h_2pow_pos : 0 < ((2 : ℝ) ^ N) := pow_pos (by norm_num) N
  have h_div : (1 : ℝ) / ((2 : ℝ) ^ N) ≤ (1 : ℝ) /
      (Finset.card (Finset.univ : Finset (JohnsonVertex N r)) : ℝ) := by
    refine (one_div_le_one_div h_2pow_pos h_card_pos).mpr ?_
    exact_mod_cast h_card_le_nat
  -- Multiply both sides by |marked| (which is ≥ 0)
  have h_result := mul_le_mul_of_nonneg_left h_div h_marked_nonneg
  -- Simplify: a * (1/b) = a/b
  simpa [div_eq_mul_inv] using h_result

/-! ### Exact marked fraction for element distinctness

When exactly one collision pair `{i, j}` exists in `f : [N] → [M]`, a vertex
(r-subset) is marked iff it contains both `i` and `j`. Among the `C(N, r)` vertices,
exactly `C(N-2, r-2)` contain a given pair, giving:

`ε = C(N-2, r-2) / C(N, r) = r(r-1) / (N(N-1))`

The proof stays in `ℕ` for as long as possible, using the combinatorial identity
`k · C(n, k) = n · C(n-1, k-1)` twice, then casts to `ℝ` at the end. -/

/-- Core combinatorial identity (in `ℕ`): `C(N-2, r-2) · N · (N-1) = C(N, r) · r · (r-1)`.
Proved by applying `Nat.add_one_mul_choose_eq` twice: once to extract `N` and `r`,
once to extract `N-1` and `r-1`. -/
lemma marked_count_mul_eq (N r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ N) :
    (Nat.choose (N - 2) (r - 2)) * N * (N - 1) = (Nat.choose N r) * r * (r - 1) := by
  have hN_pos : 1 ≤ N := by omega
  have hr_pos : 1 ≤ r := by omega
  have hN1_pos : 1 ≤ N - 1 := by omega
  have hr1_pos : 1 ≤ r - 1 := by omega
  -- First application: N·C(N-1, r-1) = C(N, r)·r
  have h_first : Nat.choose N r * r = N * Nat.choose (N - 1) (r - 1) := by
    have h := Nat.add_one_mul_choose_eq (N - 1) (r - 1)
    rw [Nat.sub_add_cancel hN_pos, Nat.sub_add_cancel hr_pos] at h
    rw [mul_comm (Nat.choose N r) r, h, mul_comm]
  -- Second application: (N-1)·C(N-2, r-2) = C(N-1, r-1)·(r-1)
  have h_second : Nat.choose (N - 1) (r - 1) * (r - 1) = (N - 1) * Nat.choose (N - 2) (r - 2) := by
    have h := Nat.add_one_mul_choose_eq (N - 2) (r - 2)
    -- h: (N-2+1) * C(N-2, r-2) = C(N-2+1, r-2+1) * (r-2+1)
    -- N-2+1 = N-1 and r-2+1 = r-1 (since N≥2, r≥2)
    have hN_succ : N - 2 + 1 = N - 1 := by omega
    have hr_succ : r - 2 + 1 = r - 1 := by omega
    rw [hN_succ, hr_succ] at h
    -- h: (N-1) * C(N-2, r-2) = C(N-1, r-1) * (r-1)
    rw [← h, mul_comm]
  -- Combine: transform LHS to RHS via h_first and h_second
  calc
    (Nat.choose (N - 2) (r - 2)) * N * (N - 1)
        = (Nat.choose (N - 2) (r - 2)) * (N * (N - 1)) := by rw [mul_assoc]
    _ = (N * (N - 1)) * Nat.choose (N - 2) (r - 2) := by rw [mul_comm]
    _ = N * ((N - 1) * Nat.choose (N - 2) (r - 2)) := by rw [mul_assoc]
    _ = N * (Nat.choose (N - 1) (r - 1) * (r - 1)) := by rw [h_second]
    _ = (N * Nat.choose (N - 1) (r - 1)) * (r - 1) := by rw [← mul_assoc]
    _ = (Nat.choose N r * r) * (r - 1) := by rw [← h_first, mul_comm]
    _ = (Nat.choose N r) * r * (r - 1) := rfl

/-- Exact marked fraction for element distinctness with one collision:
`ε = r(r-1) / (N(N-1))`. -/
lemma exact_marked_fraction (N r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ N) :
    ((Nat.choose (N - 2) (r - 2) : ℝ) / (Nat.choose N r : ℝ)) =
    ((r : ℝ) / (N : ℝ)) * (((r : ℝ) - 1) / ((N : ℝ) - 1)) := by
  have hN_pos : 1 ≤ N := by omega
  have hr_pos : 1 ≤ r := by omega
  have h_choose_pos : 0 < Nat.choose N r := Nat.choose_pos h2
  have h_choose_ne_zero : (Nat.choose N r : ℝ) ≠ 0 := by exact_mod_cast h_choose_pos.ne.symm
  have hN_ne_zero : (N : ℝ) ≠ 0 := by
    have hN_pos' : 0 < N := by omega
    exact_mod_cast hN_pos'.ne.symm
  have hN1_ne_zero : ((N : ℝ) - 1) ≠ 0 := by
    intro hzero
    have : (N : ℝ) = 1 := by linarith
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 ≤ N by omega)
    linarith
  field_simp [h_choose_ne_zero, hN_ne_zero, hN1_ne_zero]
  -- Goal: ↑C(N-2,r-2) * ↑N * (↑N - 1) = ↑C(N,r) * ↑r * (↑r - 1)
  have h_nat := marked_count_mul_eq N r h1 h2
  -- Cast the ℕ identity to ℝ
  have h_cast := congrArg (fun x : ℕ => (x : ℝ)) h_nat
  -- h_cast: ↑(C(N-2,r-2) * N * (N-1)) = ↑(C(N,r) * r * (r-1))
  push_cast at h_cast
  -- h_cast: ↑C(N-2,r-2) * ↑N * ↑(N-1) = ↑C(N,r) * ↑r * ↑(r-1)
  -- Convert ↑(N-1) to (↑N - 1): both sides
  rw [Nat.cast_sub hN_pos, Nat.cast_sub hr_pos] at h_cast
  -- h_cast: ↑C(N-2,r-2) * ↑N * (↑N - ↑1) = ↑C(N,r) * ↑r * (↑r - ↑1)
  -- But ↑1 = (1 : ℝ), and the goal has (↑N - 1) not (↑N - ↑1)
  -- We can use `Nat.cast_one` or just let `simp` handle it
  simpa [Nat.cast_one] using h_cast

/-! ### Adjacency action on zero-sum subset functions

For `f_v(R) = Σ_{x∈R} v_x` and `Σ_x v_x = 0`, summing over neighbours
returns `(degree - N) * f_v(R)`. This identifies candidate eigenvectors;
it does not order the full spectrum or prove a spectral gap. -/

/-- The "sum over R" eigenvector candidate: f_v(R) = Σ_{x∈R.val} v_x. -/
def candidateEigenvector (v : Fin N → ℝ) (R : JohnsonVertex N r) : ℝ :=
  ∑ x ∈ R.val, v x

lemma candidateEigenvector_swapSet (v : Fin N → ℝ) (R : JohnsonVertex N r)
    (u : Fin N) (hu : u ∈ R.val) (w : Fin N) (hw : w ∉ R.val) :
    candidateEigenvector v (swapSet R u hu w hw) = candidateEigenvector v R - v u + v w := by
  unfold candidateEigenvector
  dsimp [swapSet]
  have h_disjoint : Disjoint (R.val.erase u) {w} :=
    Finset.disjoint_singleton_right.mpr (by simp [hw])
  rw [Finset.sum_union h_disjoint, Finset.sum_singleton]
  rw [← Finset.sum_erase_add R.val (v ·) hu]
  ring

/-- Complement sum trick: Σ_{w∉R} v_w = -f_v(R), using Σ_all v = 0. -/
lemma sum_compl_eq_neg_candidateEigenvector (v : Fin N → ℝ) (hv : ∑ x : Fin N, v x = 0)
    (R : JohnsonVertex N r) : ∑ w ∈ (Finset.univ \ R.val), v w = - candidateEigenvector v R := by
  have h := Finset.sum_add_sum_compl (R.val) (v ·)
  rw [hv] at h
  have h' : (∑ x ∈ (R.val)ᶜ, v x) = - (∑ x ∈ R.val, v x) := by linarith
  -- (R.val)ᶜ = Finset.univ \ R.val definitionally in mathlib4
  unfold candidateEigenvector
  exact h'

/-- Sum of f_v over all neighbours of R equals (d - N)·f_v(R).

Type-erasure proof: project to `Finset (Fin N)`, use `sum_image` + `sum_product`. -/
lemma sum_candidateEigenvector_over_neighbors (hr_pos : 0 < r) (hr_lt_N : r < N)
    (v : Fin N → ℝ) (hv : ∑ x : Fin N, v x = 0) (R : JohnsonVertex N r) :
    (∑ R' ∈ neighbors R, candidateEigenvector v R') =
    ((degree N r : ℝ) - (N : ℝ)) * candidateEigenvector v R := by
  -- Local binding to avoid ↑R coercion issues
  let RV : Finset (Fin N) := R.val
  -- Raw functions on Finset (Fin N) — no Subtype proofs needed
  let f_raw (S : Finset (Fin N)) : ℝ := ∑ x ∈ S, v x
  have h_f_raw_eq : ∀ (R' : JohnsonVertex N r), f_raw R'.val = candidateEigenvector v R' := by
    intro R'; rfl
  let swap_raw (S : Finset (Fin N)) (u w : Fin N) : Finset (Fin N) :=
    insert w (erase S u)
  -- swap_raw = (swapSet ...).val when membership holds
  have h_swap_raw_val : ∀ (u : Fin N) (hu : u ∈ RV) (w : Fin N) (hw : w ∉ RV),
      swap_raw RV u w = (swapSet R u hu w hw).val := by
    intro u hu w hw; dsimp [swap_raw, swapSet, RV]; simp
  -- Step 1: Project neighbours to raw Finsets via Finset.map with Embedding
  let φ : JohnsonVertex N r ↪ Finset (Fin N) :=
    { toFun := fun R' => R'.val
      inj' := by intro a b h; apply Subtype.ext; exact h }
  have h_step1 : (∑ R' ∈ neighbors R, candidateEigenvector v R') =
      (∑ S ∈ (neighbors R).map φ, f_raw S) := by
    rw [Finset.sum_map]
    rfl
  rw [h_step1]
  -- Step 2: Set equality — map φ (neighbors) = image of product under swap_raw
  let T := (Finset.univ : Finset (Fin N)) \ RV
  have h_map_eq_image : (neighbors R).map φ = (neighbors R).image (fun (R' : JohnsonVertex N r) =>
    R'.val) := by
    rw [Finset.map_eq_image]
    rfl
  rw [h_map_eq_image]
  have h_set_eq : (neighbors R).image (fun (R' : JohnsonVertex N r) => R'.val) =
      (RV ×ˢ T).image (fun (p : Fin N × Fin N) => swap_raw RV p.1 p.2) := by
    ext S
    constructor
    · intro h_mem
      rw [Finset.mem_image] at h_mem
      rcases h_mem with ⟨R', hR'_adj, rfl⟩
      -- R' is a neighbour, so ∃ u∈R, w∉R with swapSet R u w = R'
      have h_adj : isAdjacent R R' := by
        rw [neighbors, Finset.mem_filter] at hR'_adj; exact hR'_adj.2
      let u := uniqueRemoved h_adj hr_pos
      let w := uniqueAdded h_adj hr_pos
      have hu : u ∈ R.val := (uniqueRemoved_mem h_adj hr_pos).1
      have hw : w ∈ T := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (uniqueAdded_mem h_adj hr_pos).1⟩
      have h_swap_eq_val : swap_raw R.val u w = R'.val := by
        rw [h_swap_raw_val u hu w (Finset.mem_sdiff.mp hw).2, swapSet_reconstruct h_adj hr_pos]
      rw [Finset.mem_image]
      exact ⟨(u, w), Finset.mem_product.mpr ⟨hu, hw⟩, h_swap_eq_val⟩
    · intro h_mem
      rw [Finset.mem_image] at h_mem
      rcases h_mem with ⟨⟨u, w⟩, h_prod, rfl⟩
      rw [Finset.mem_product] at h_prod
      rcases h_prod with ⟨hu, hw⟩
      rcases Finset.mem_sdiff.mp hw with ⟨_, hw_not⟩
      rw [Finset.mem_image]
      have h_swap_val : swap_raw R.val u w = (swapSet R u hu w hw_not).val :=
        h_swap_raw_val u hu w hw_not
      rw [h_swap_val]
      refine ⟨swapSet R u hu w hw_not, ?_, rfl⟩
      rw [neighbors, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, isAdjacent_swapSet R u hu w hw_not⟩
  rw [h_set_eq]
  -- Step 3: Finset.sum_image (injectivity via sdiff lemmas)
  have h_inj : ∀ (x y : Fin N × Fin N), x ∈ RV ×ˢ T → y ∈ RV ×ˢ T →
      swap_raw RV x.1 x.2 = swap_raw RV y.1 y.2 → x = y := by
    intro x y hx hy h_eq
    rcases x with ⟨ux, wx⟩; rcases y with ⟨uy, wy⟩
    rw [Finset.mem_product] at hx hy
    rcases hx with ⟨hux, hwx⟩; rcases hy with ⟨huy, hwy⟩
    rcases Finset.mem_sdiff.mp hwx with ⟨_, hwx_not⟩
    rcases Finset.mem_sdiff.mp hwy with ⟨_, hwy_not⟩
    rw [h_swap_raw_val ux hux wx hwx_not, h_swap_raw_val uy huy wy hwy_not] at h_eq
    -- Use sdiff lemmas for uniqueness of u, w
    have h_sdiff_ux : RV \ (swapSet R ux hux wx hwx_not).val = {ux} := by
      dsimp [RV]; exact sdiff_swapSet_eq_singleton R ux hux wx hwx_not
    have h_sdiff_uy : RV \ (swapSet R uy huy wy hwy_not).val = {uy} := by
      dsimp [RV]; exact sdiff_swapSet_eq_singleton R uy huy wy hwy_not
    rw [h_eq] at h_sdiff_ux
    rw [h_sdiff_uy] at h_sdiff_ux
    have h_u_eq : ux = uy := (Finset.singleton_inj.mp h_sdiff_ux).symm
    have h_sdiff_wx : (swapSet R ux hux wx hwx_not).val \ RV = {wx} := by
      dsimp [RV]; exact swapSet_sdiff_eq_singleton R ux hux wx hwx_not
    have h_sdiff_wy : (swapSet R uy huy wy hwy_not).val \ RV = {wy} := by
      dsimp [RV]; exact swapSet_sdiff_eq_singleton R uy huy wy hwy_not
    rw [h_eq] at h_sdiff_wx
    rw [h_sdiff_wy] at h_sdiff_wx
    have h_w_eq : wx = wy := (Finset.singleton_inj.mp h_sdiff_wx).symm
    exact Prod.ext h_u_eq h_w_eq
  -- Finset.sum_image: image_sum = domain_sum
  rw [Finset.sum_image (fun x hx y hy h => h_inj x y hx hy h)]
  -- Step 4: Finset.sum_product → double sum
  rw [Finset.sum_product]
  -- Step 5: Expand each term via candidateEigenvector_swapSet
  have h_expand : ∀ u ∈ RV, ∀ w ∈ T,
      f_raw (swap_raw RV u w) = candidateEigenvector v R - v u + v w := by
    intro u hu w hw
    have hw_not : w ∉ R.val := by
      rw [Finset.mem_sdiff] at hw; exact hw.2
    rw [h_swap_raw_val u hu w hw_not, h_f_raw_eq (swapSet R u hu w hw_not),
      candidateEigenvector_swapSet v R u hu w hw_not]
  rw [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun w hw => h_expand u hu w hw))]
  -- Now: ∑ u ∈ RV, ∑ w ∈ T, (candidateEigenvector v R - v u + v w)
  -- Step 6: Distribute and compute
  have h_card_RV : RV.card = r := by dsimp [RV]; exact R.property
  have h_card_T : T.card = N - r := by
    dsimp [T, RV]
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R.val)
    rw [R.property, Finset.card_fin] at h
    omega
  -- Expand: ∑_u ∑_w (f - v_u + v_w) = T1 + T2 + T3
  have h_inner (u : Fin N) : (∑ w ∈ T, (candidateEigenvector v R - v u + v w)) =
      ((T.card : ℝ) * candidateEigenvector v R) + ((T.card : ℝ) * (- v u)) + (∑ w ∈ T, v w) := by
    calc
      (∑ w ∈ T, (candidateEigenvector v R - v u + v w))
          = (∑ w ∈ T, ((candidateEigenvector v R - v u) + v w)) := rfl
      _ = (∑ w ∈ T, (candidateEigenvector v R - v u)) + (∑ w ∈ T, v w) := by rw
        [Finset.sum_add_distrib]
      _ = ((∑ w ∈ T, candidateEigenvector v R) - (∑ w ∈ T, v u)) + (∑ w ∈ T, v w) := by rw
        [Finset.sum_sub_distrib]
      _ = (((T.card : ℝ) * candidateEigenvector v R) - ((T.card : ℝ) * v u)) + (∑ w ∈ T, v w) :=
        by simp
      _ = ((T.card : ℝ) * candidateEigenvector v R) + ((T.card : ℝ) * (- v u)) + (∑ w ∈ T, v w) :=
        by ring
  rw [Finset.sum_congr rfl (fun u hu => h_inner u)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- T1: ∑_u (|T|·f(R)) = |RV|·|T|·f(R) = r·(N-r)·f(R)
  -- Cast card_T to ℝ properly (Nat.cast_sub needed)
  have hT_real : (T.card : ℝ) = (N : ℝ) - (r : ℝ) := by
    rw [h_card_T, Nat.cast_sub (Nat.le_of_lt hr_lt_N)]
  have hT1 : (∑ u ∈ RV, ((T.card : ℝ) * candidateEigenvector v R)) =
      ((r : ℝ) * ((N : ℝ) - (r : ℝ))) * candidateEigenvector v R := by
    calc
      (∑ u ∈ RV, ((T.card : ℝ) * candidateEigenvector v R))
          = ((RV.card : ℝ) * ((T.card : ℝ) * candidateEigenvector v R)) := by simp
      _ = ((r : ℝ) * ((T.card : ℝ) * candidateEigenvector v R)) := by simp [h_card_RV]
      _ = ((r : ℝ) * (((N : ℝ) - (r : ℝ)) * candidateEigenvector v R)) := by rw [hT_real]
      _ = ((r : ℝ) * ((N : ℝ) - (r : ℝ))) * candidateEigenvector v R := by ring
  -- T2: ∑_u (|T|·(-v_u)) = -|T|·∑_u v_u = -(N-r)·f(R)
  have hT2 : (∑ u ∈ RV, ((T.card : ℝ) * (- v u))) =
      -(((N : ℝ) - (r : ℝ)) * candidateEigenvector v R) := by
    calc
      (∑ u ∈ RV, ((T.card : ℝ) * (- v u)))
          = ((T.card : ℝ) * (∑ u ∈ RV, (- v u))) := by simp [Finset.mul_sum]
      _ = ((T.card : ℝ) * (- (∑ u ∈ RV, v u))) := by simp
      _ = (((N : ℝ) - (r : ℝ)) * (- (∑ u ∈ RV, v u))) := by rw [hT_real]
      _ = (((N : ℝ) - (r : ℝ)) * (- candidateEigenvector v R)) := by simp [candidateEigenvector, RV]
      _ = -(((N : ℝ) - (r : ℝ)) * candidateEigenvector v R) := by ring
  -- T3: ∑_u (∑_w v_w) = |RV|·∑_w v_w = r·(-f(R))
  have hT3 : (∑ u ∈ RV, (∑ w ∈ T, v w)) = (r : ℝ) * (- candidateEigenvector v R) := by
    calc
      (∑ u ∈ RV, (∑ w ∈ T, v w)) = ((RV.card : ℝ) * (∑ w ∈ T, v w)) := by simp [Finset.mul_sum]
      _ = (r : ℝ) * (∑ w ∈ T, v w) := by simp [h_card_RV]
      _ = (r : ℝ) * (- candidateEigenvector v R) := by
        dsimp [T, RV]; rw [sum_compl_eq_neg_candidateEigenvector v hv R]
  rw [hT1, hT2, hT3]
  -- Goal: r*(N-r)*f - (N-r)*f - r*f = (r*(N-r) - N)*f (with casts)
  unfold degree
  push_cast
  rw [Nat.cast_sub (Nat.le_of_lt hr_lt_N)]
  ring


/-- Arithmetic inequality `N/(r(N-r)) ≥ 1/r` for `0 < r < N`. -/
lemma degree_ratio_ge_one_div_r (hr_pos : 0 < r) (hr_lt_N : r < N) :
    (N : ℝ) / (degree N r : ℝ) ≥ 1 / (r : ℝ) := by
  have hr_pos' : 0 < (r : ℝ) := by exact_mod_cast hr_pos
  have h_deg_pos : 0 < (degree N r : ℝ) := by exact_mod_cast degree_pos hr_pos hr_lt_N
  have h_diff_eq : (N : ℝ) / (degree N r : ℝ) - 1 / (r : ℝ) =
      ((r : ℝ) * (r : ℝ)) / ((degree N r : ℝ) * (r : ℝ)) := by
    field_simp [hr_pos'.ne.symm, h_deg_pos.ne.symm]
    unfold degree
    have h_le : r ≤ N := Nat.le_of_lt hr_lt_N
    push_cast
    rw [Nat.cast_sub h_le]
    ring
  have h_nonneg : 0 ≤ ((r : ℝ) * (r : ℝ)) / ((degree N r : ℝ) * (r : ℝ)) :=
    div_nonneg (by positivity) (by positivity)
  linarith

/-! ### Exact ε lower bound with 1/2 relaxation

The exact formula `ε = r(r-1)/(N(N-1))` is always **strictly less** than `(r/N)²`
when `r < N`.  We prove the weaker but universally true bound
`ε ≥ (1/2)·(r/N)²` for `r ≥ 2`, using the elementary inequality `r-1 ≥ r/2`. -/

/-- For `r ≥ 2`, we have `r(r-1)/(N(N-1)) ≥ (1/2)·(r/N)²`.
Proof: `r-1 ≥ r/2` and `N-1 < N`, then cross-multiply. -/
lemma exact_epsilon_lower_bound (N r : ℕ) (hr_ge_2 : 2 ≤ r) (hr_lt_N : r < N) :
    ((r : ℝ) / (N : ℝ)) * (((r : ℝ) - 1) / ((N : ℝ) - 1)) ≥
    (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2) := by
  have hr_pos : 0 < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) hr_ge_2
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by omega) hr_lt_N
  have hN1_pos : 0 < (N : ℝ) - 1 := by
    have h : 1 < N := by omega
    exact sub_pos.mpr (by exact_mod_cast h)
  -- Cancel (r/N) from both sides; reduce to (r-1)/(N-1) ≥ (r/2)/N
  have h_reduced : ((r : ℝ) - 1) / ((N : ℝ) - 1) ≥ ((r : ℝ) / 2) / (N : ℝ) := by
    -- (r-1)*(1/(N-1)) ≥ (r/2)*(1/N) since r-1 ≥ r/2 and 1/(N-1) ≥ 1/N
    have h_num : (r : ℝ) - 1 ≥ (r : ℝ) / 2 := by
      have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr_ge_2
      linarith
    have h_denom_le : (N : ℝ) - 1 ≤ (N : ℝ) := sub_le_self _ (by positivity)
    have h_denom : 1 / ((N : ℝ) - 1) ≥ 1 / (N : ℝ) :=
      (one_div_le_one_div hN_pos hN1_pos).mpr h_denom_le
    have h_nonneg_r : 0 ≤ (r : ℝ) := by positivity
    have h_nonneg_r1 : 0 ≤ (r : ℝ) - 1 := by linarith
    -- (r-1)*(1/(N-1)) ≥ (r/2)*(1/N)
    have h_prod : ((r : ℝ) - 1) * (1 / ((N : ℝ) - 1)) ≥ ((r : ℝ) / 2) * (1 / (N : ℝ)) :=
      mul_le_mul h_num h_denom (by positivity) h_nonneg_r1
    -- Convert back to division form
    simpa [div_eq_mul_inv] using h_prod
  have h_nonneg_rN : 0 ≤ (r : ℝ) / (N : ℝ) := div_nonneg (by positivity) (by positivity)
  -- Multiply both sides by (r/N) ≥ 0
  calc
    ((r : ℝ) / (N : ℝ)) * (((r : ℝ) - 1) / ((N : ℝ) - 1))
        ≥ ((r : ℝ) / (N : ℝ)) * (((r : ℝ) / 2) / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left h_reduced h_nonneg_rN
    _ = (1/2 : ℝ) * (((r : ℝ) / (N : ℝ)) ^ 2) := by ring

end JohnsonVertex

end QuantumAlg
