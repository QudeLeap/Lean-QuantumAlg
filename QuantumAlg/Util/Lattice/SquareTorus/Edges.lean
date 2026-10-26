/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates

/-!
# Coverage of the periodic square bonds

Horizontal and vertical bonds each have one positively oriented starting site.
The two tile colours cover these sites bijectively, so no physical bond is
dropped or repeated, including across periodic boundaries.
-/

@[expose] public section

namespace SquareTorus

/-- Positive horizontal neighbour. -/
def right {L : ℕ} (p : Site L) : Site L := (p.1, next p.2)

/-- Positive vertical neighbour. -/
def down {L : ℕ} (p : Site L) : Site L := (next p.1, p.2)

/-- Start of one of the two horizontal bonds of a tile. -/
def horizontalStart {L : ℕ} (colour : Fin 2) (a : Tile L) (b : Fin 2) : Site L :=
  corner colour a (b, 0)

/-- Start of one of the two vertical bonds of a tile. -/
def verticalStart {L : ℕ} (colour : Fin 2) (a : Tile L) (b : Fin 2) : Site L :=
  corner colour a (0, b)

lemma right_horizontalStart {L : ℕ} (colour : Fin 2) (a : Tile L) (b : Fin 2) :
    right (horizontalStart colour a b) = corner colour a (b, 1) := by
  simp [right, horizontalStart, corner, tileCoord_one]

lemma down_verticalStart {L : ℕ} (colour : Fin 2) (a : Tile L) (b : Fin 2) :
    down (verticalStart colour a b) = corner colour a (1, b) := by
  simp [down, verticalStart, corner, tileCoord_one]

/-- Colours, tiles and within-tile rows cover each horizontal bond once. -/
def horizontalEquiv {L : ℕ} (hL : Even L) : (Fin 2 × Tile L × Fin 2) ≃ Site L where
  toFun p := horizontalStart p.1 p.2.1 p.2.2
  invFun p :=
    let c := (pairEquiv hL).symm p.2
    let r := (tileEquiv hL c.2).symm p.1
    (c.2, (r.1, c.1), r.2)
  left_inv := by
    rintro ⟨c, ⟨a, b⟩, x⟩
    dsimp only [horizontalStart, corner]
    rw [tileCoord_zero, ← pairEquiv_apply hL, Equiv.symm_apply_apply]
    simp only [← tileEquiv_apply hL, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only [horizontalStart, corner]
    rw [tileCoord_zero]
    simp only [← pairEquiv_apply hL, ← tileEquiv_apply hL,
      Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] lemma horizontalEquiv_apply {L : ℕ} (hL : Even L)
    (c : Fin 2) (a : Tile L) (b : Fin 2) :
    horizontalEquiv hL (c, a, b) = horizontalStart c a b := rfl

/-- Colours, tiles and within-tile columns cover each vertical bond once. -/
def verticalEquiv {L : ℕ} (hL : Even L) : (Fin 2 × Tile L × Fin 2) ≃ Site L where
  toFun p := verticalStart p.1 p.2.1 p.2.2
  invFun p :=
    let r := (pairEquiv hL).symm p.1
    let c := (tileEquiv hL r.2).symm p.2
    (r.2, (r.1, c.1), c.2)
  left_inv := by
    rintro ⟨c, ⟨a, b⟩, x⟩
    dsimp only [verticalStart, corner]
    rw [tileCoord_zero, ← pairEquiv_apply hL, Equiv.symm_apply_apply]
    simp only [← tileEquiv_apply hL, Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨a, b⟩
    dsimp only [verticalStart, corner]
    rw [tileCoord_zero]
    simp only [← pairEquiv_apply hL, ← tileEquiv_apply hL,
      Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] lemma verticalEquiv_apply {L : ℕ} (hL : Even L)
    (c : Fin 2) (a : Tile L) (b : Fin 2) :
    verticalEquiv hL (c, a, b) = verticalStart c a b := rfl

/-- Reindex any horizontal-bond sum by its unique coloured tile occurrence. -/
lemma sum_horizontalStart {L : ℕ} (hL : Even L) {M : Type*} [AddCommMonoid M]
    (f : Site L → M) :
    (∑ c : Fin 2, ∑ a : Tile L, ∑ b : Fin 2, f (horizontalStart c a b)) = ∑ p, f p := by
  simpa only [Fintype.sum_prod_type, horizontalEquiv_apply] using
    (horizontalEquiv hL).sum_comp f

/-- Reindex any vertical-bond sum by its unique coloured tile occurrence. -/
lemma sum_verticalStart {L : ℕ} (hL : Even L) {M : Type*} [AddCommMonoid M]
    (f : Site L → M) :
    (∑ c : Fin 2, ∑ a : Tile L, ∑ b : Fin 2, f (verticalStart c a b)) = ∑ p, f p := by
  simpa only [Fintype.sum_prod_type, verticalEquiv_apply] using
    (verticalEquiv hL).sum_comp f

lemma right_ne_self {L : ℕ} (hL : 2 ≤ L) (p : Site L) : right p ≠ p := by
  intro h
  exact next_ne hL p.2 (congrArg Prod.snd h)

lemma down_ne_self {L : ℕ} (hL : 2 ≤ L) (p : Site L) : down p ≠ p := by
  intro h
  exact next_ne hL p.1 (congrArg Prod.fst h)

end SquareTorus
