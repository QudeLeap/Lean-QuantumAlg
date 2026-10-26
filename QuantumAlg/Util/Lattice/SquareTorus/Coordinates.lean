/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

/-!
# Periodic square coordinates

An even square torus is tiled by disjoint two-by-two squares in each of two
diagonally translated colours. All coordinate maps retain periodic wrap edges.
The definitions are total; the tiling equivalences require an even side length.
-/

@[expose] public section

namespace SquareTorus

/-- Row and column of a square lattice. -/
abbrev Site (L : ℕ) := Fin L × Fin L

/-- Row and column of a two-by-two tile. -/
abbrev Tile (L : ℕ) := Fin (L / 2) × Fin (L / 2)

/-- Forward periodic neighbour. -/
def next {L : ℕ} (j : Fin L) : Fin L :=
  ⟨if j.val + 1 < L then j.val + 1 else 0, by
    split_ifs with h
    · exact h
    · exact j.pos⟩

/-- Backward periodic neighbour. -/
def prev {L : ℕ} (j : Fin L) : Fin L :=
  ⟨if j.val = 0 then L - 1 else j.val - 1, by
    have := j.isLt
    have := j.pos
    split_ifs <;> omega⟩

@[simp] lemma next_val {L : ℕ} (j : Fin L) :
    (next j).val = if j.val + 1 < L then j.val + 1 else 0 := rfl

@[simp] lemma prev_val {L : ℕ} (j : Fin L) :
    (prev j).val = if j.val = 0 then L - 1 else j.val - 1 := rfl

@[simp] lemma prev_next {L : ℕ} (j : Fin L) : prev (next j) = j := by
  apply Fin.ext
  simp only [prev_val, next_val]
  have := j.isLt
  have := j.pos
  by_cases h : j.val + 1 < L
  · simp [h]
  · have hj : j.val = L - 1 := by omega
    simpa only [if_neg h, ↓reduceIte] using hj.symm

@[simp] lemma next_prev {L : ℕ} (j : Fin L) : next (prev j) = j := by
  apply Fin.ext
  simp only [prev_val, next_val]
  have := j.isLt
  have := j.pos
  split_ifs <;> omega

/-- Periodic translation is a permutation, including the empty coordinate type. -/
def nextEquiv (L : ℕ) : Equiv.Perm (Fin L) where
  toFun := next
  invFun := prev
  left_inv := prev_next
  right_inv := next_prev

lemma next_ne {L : ℕ} (hL : 2 ≤ L) (j : Fin L) : next j ≠ j := by
  intro h
  have hval := congrArg Fin.val h
  simp only [next_val] at hval
  have := j.isLt
  split_ifs at hval <;> omega

/-- A cell in the unshifted partition into pairs. -/
def pairCoord {L : ℕ} (a : Fin (L / 2)) (b : Fin 2) : Fin L :=
  ⟨2 * a.val + b.val, by have := a.isLt; have := b.isLt; omega⟩

@[simp] lemma pairCoord_val {L : ℕ} (a : Fin (L / 2)) (b : Fin 2) :
    (pairCoord a b).val = 2 * a.val + b.val := rfl

lemma even_twice_half {L : ℕ} (hL : Even L) : L / 2 * 2 = L := by
  obtain ⟨k, hk⟩ := hL
  omega

/-- Even coordinates are partitioned exactly by pair and within-pair index. -/
def pairEquiv {L : ℕ} (hL : Even L) : (Fin (L / 2) × Fin 2) ≃ Fin L :=
  finProdFinEquiv.trans (finCongr (even_twice_half hL))

@[simp] lemma pairEquiv_apply {L : ℕ} (hL : Even L)
    (a : Fin (L / 2)) (b : Fin 2) : pairEquiv hL (a, b) = pairCoord a b := by
  apply Fin.ext
  simp [pairEquiv, pairCoord, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

lemma next_pair_zero {L : ℕ} (a : Fin (L / 2)) :
    next (pairCoord a 0) = pairCoord a 1 := by
  apply Fin.ext
  simp only [next_val, pairCoord_val, Fin.val_zero, Fin.val_one, Nat.add_zero]
  have := a.isLt
  have h : 2 * a.val + 1 < L := by omega
  simp [h]

/-- A within-tile coordinate, translated by one for the second colour. -/
def tileCoord {L : ℕ} (colour : Fin 2) (a : Fin (L / 2)) (b : Fin 2) : Fin L :=
  if colour.val = 0 then pairCoord a b else next (pairCoord a b)

/-- Each colour partitions one periodic coordinate exactly. -/
def tileEquiv {L : ℕ} (hL : Even L) (colour : Fin 2) :
    (Fin (L / 2) × Fin 2) ≃ Fin L :=
  if colour.val = 0 then pairEquiv hL else (pairEquiv hL).trans (nextEquiv L)

@[simp] lemma tileEquiv_apply {L : ℕ} (hL : Even L) (colour : Fin 2)
    (a : Fin (L / 2)) (b : Fin 2) : tileEquiv hL colour (a, b) = tileCoord colour a b := by
  simp only [tileEquiv, tileCoord]
  split_ifs <;> simp [pairEquiv_apply, nextEquiv]

lemma tileCoord_zero {L : ℕ} (colour : Fin 2) (a : Fin (L / 2)) :
    tileCoord colour a 0 = pairCoord a colour := by
  fin_cases colour <;> simp [tileCoord, next_pair_zero]

lemma tileCoord_one {L : ℕ} (colour : Fin 2) (a : Fin (L / 2)) :
    tileCoord colour a 1 = next (tileCoord colour a 0) := by
  simp only [tileCoord]
  split_ifs <;> rw [next_pair_zero]

/-- A corner of a coloured two-by-two tile. -/
def corner {L : ℕ} (colour : Fin 2) (a : Tile L) (b : Fin 2 × Fin 2) : Site L :=
  (tileCoord colour a.1 b.1, tileCoord colour a.2 b.2)

/-- Every site has a unique tile and corner in each colour. -/
def cornerEquiv {L : ℕ} (hL : Even L) (colour : Fin 2) :
    (Tile L × (Fin 2 × Fin 2)) ≃ Site L where
  toFun ab := corner colour ab.1 ab.2
  invFun p :=
    ((((tileEquiv hL colour).symm p.1).1, ((tileEquiv hL colour).symm p.2).1),
      (((tileEquiv hL colour).symm p.1).2, ((tileEquiv hL colour).symm p.2).2))
  left_inv := by
    rintro ⟨⟨a, b⟩, c, d⟩
    simp only [corner, ← tileEquiv_apply hL, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a, b⟩
    simp only [corner, ← tileEquiv_apply hL, Prod.mk.eta, Equiv.apply_symm_apply]

lemma corner_injective {L : ℕ} (hL : Even L) (colour : Fin 2) :
    Function.Injective (fun ab : Tile L × (Fin 2 × Fin 2) => corner colour ab.1 ab.2) :=
  (cornerEquiv hL colour).injective

/-- Distinct tiles of one colour have no site in common. -/
lemma corners_ne_of_tile_ne {L : ℕ} (hL : Even L) (colour : Fin 2)
    {a b : Tile L} (hab : a ≠ b) (x y : Fin 2 × Fin 2) :
    corner colour a x ≠ corner colour b y := by
  intro h
  have heq : (a, x) = (b, y) := corner_injective hL colour h
  exact hab (congrArg Prod.fst heq)

/-- The row-snake order reverses columns precisely in odd rows. -/
def snakeColumn {L : ℕ} (row column : Fin L) : Fin L :=
  if row.val % 2 = 0 then column else column.rev

@[simp] lemma snakeColumn_twice {L : ℕ} (row column : Fin L) :
    snakeColumn row (snakeColumn row column) = column := by
  simp only [snakeColumn]
  split_ifs <;> simp

/-- Row-major indexing after the row-snake permutation. -/
def snakeIndex {L : ℕ} (p : Site L) : Fin (L ^ 2) :=
  Fin.cast (pow_two L).symm (finProdFinEquiv (p.1, snakeColumn p.1 p.2))

lemma snakeIndex_val_column {L : ℕ} (p : Site L) :
    (snakeIndex p).val = L * p.1.val + (snakeColumn p.1 p.2).val := by
  change (snakeColumn p.1 p.2).val + L * p.1.val = _
  omega

@[simp] lemma snakeIndex_val {L : ℕ} (p : Site L) :
    (snakeIndex p).val = L * p.1.val +
      (if p.1.val % 2 = 0 then p.2.val else L - 1 - p.2.val) := by
  change (snakeColumn p.1 p.2).val + L * p.1.val = _
  by_cases h : p.1.val % 2 = 0
  · simp [snakeColumn, h, Nat.add_comm]
  · simp [snakeColumn, h, Fin.rev, Nat.sub_sub, Nat.add_comm]

/-- The row-snake indexing is a bijection onto all square positions. -/
def snakeEquiv (L : ℕ) : Site L ≃ Fin (L ^ 2) :=
  (Equiv.prodCongrRight fun r =>
    if r.val % 2 = 0 then Equiv.refl (Fin L) else Fin.revPerm).trans
    (finProdFinEquiv.trans (finCongr (pow_two L).symm))

@[simp] lemma snakeEquiv_apply {L : ℕ} (p : Site L) : snakeEquiv L p = snakeIndex p := by
  apply Fin.ext
  by_cases h : p.1.val % 2 = 0 <;>
    simp [snakeEquiv, snakeIndex, snakeColumn, h, finProdFinEquiv]

end SquareTorus
