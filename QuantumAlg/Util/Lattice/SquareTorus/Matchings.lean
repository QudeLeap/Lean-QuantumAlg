/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import all QuantumAlg.Util.Lattice.SquareTorus.Coordinates
import Mathlib.Tactic

/-!
# The two periodic perfect matchings in each coordinate

Flipping the endpoint in a colored pair defines a fixed-point-free
involution. Horizontal and vertical flips commute, including when their
colors differ.
-/

@[expose] public section

namespace SquareTorus

/-- Exchange the endpoints of the unique colored pair containing a coordinate. -/
def coordinateMatching {L : ℕ} (hL : Even L) (c : Fin 2) : Equiv.Perm (Fin L) :=
  (tileEquiv hL c).symm.trans
    ((Equiv.prodCongr (Equiv.refl _) Fin.revPerm).trans (tileEquiv hL c))

@[simp] lemma coordinateMatching_tileCoord {L : ℕ} (hL : Even L)
    (c : Fin 2) (a : Fin (L / 2)) (b : Fin 2) :
    coordinateMatching hL c (tileCoord c a b) = tileCoord c a b.rev := by
  unfold coordinateMatching
  simp only [Equiv.trans_apply]
  rw [← tileEquiv_apply hL c a b, Equiv.symm_apply_apply]
  exact tileEquiv_apply hL c a b.rev

@[simp] lemma coordinateMatching_twice {L : ℕ} (hL : Even L)
    (c : Fin 2) (j : Fin L) :
    coordinateMatching hL c (coordinateMatching hL c j) = j := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (tileEquiv hL c).surjective j
  rw [tileEquiv_apply, coordinateMatching_tileCoord, coordinateMatching_tileCoord,
    Fin.rev_rev]

lemma coordinateMatching_ne {L : ℕ} (hL : Even L) (c : Fin 2) (j : Fin L) :
    j ≠ coordinateMatching hL c j := by
  obtain ⟨⟨a, b⟩, rfl⟩ := (tileEquiv hL c).surjective j
  rw [tileEquiv_apply, coordinateMatching_tileCoord]
  intro h
  have heq : (a, b) = (a, b.rev) := (tileEquiv hL c).injective (by
    simpa only [tileEquiv_apply] using h)
  have hb := congrArg Prod.snd heq
  fin_cases b <;> simp at hb

lemma coordinateMatching_symm {L : ℕ} (hL : Even L) (c : Fin 2) :
    (coordinateMatching hL c).symm = coordinateMatching hL c := by
  apply Equiv.ext
  intro j
  apply (coordinateMatching hL c).injective
  simp

/-- Exchange the horizontal endpoints of each colored plaquette. -/
def horizontalMatching {L : ℕ} (hL : Even L) (c : Fin 2) : Equiv.Perm (Site L) :=
  Equiv.prodCongr (Equiv.refl _) (coordinateMatching hL c)

/-- Exchange the vertical endpoints of each colored plaquette. -/
def verticalMatching {L : ℕ} (hL : Even L) (c : Fin 2) : Equiv.Perm (Site L) :=
  Equiv.prodCongr (coordinateMatching hL c) (Equiv.refl _)

@[simp] lemma horizontalMatching_corner {L : ℕ} (hL : Even L) (c : Fin 2)
    (a : Tile L) (b : Fin 2 × Fin 2) :
    horizontalMatching hL c (corner c a b) = corner c a (b.1, b.2.rev) := by
  simp [horizontalMatching, corner]

@[simp] lemma verticalMatching_corner {L : ℕ} (hL : Even L) (c : Fin 2)
    (a : Tile L) (b : Fin 2 × Fin 2) :
    verticalMatching hL c (corner c a b) = corner c a (b.1.rev, b.2) := by
  simp [verticalMatching, corner]

@[simp] lemma horizontalMatching_twice {L : ℕ} (hL : Even L)
    (c : Fin 2) (p : Site L) :
    horizontalMatching hL c (horizontalMatching hL c p) = p := by
  rcases p with ⟨x, y⟩
  simp [horizontalMatching]

@[simp] lemma verticalMatching_twice {L : ℕ} (hL : Even L)
    (c : Fin 2) (p : Site L) :
    verticalMatching hL c (verticalMatching hL c p) = p := by
  rcases p with ⟨x, y⟩
  simp [verticalMatching]

lemma horizontalMatching_ne {L : ℕ} (hL : Even L) (c : Fin 2) (p : Site L) :
    p ≠ horizontalMatching hL c p := by
  intro h
  exact coordinateMatching_ne hL c p.2 (congrArg Prod.snd h)

lemma verticalMatching_ne {L : ℕ} (hL : Even L) (c : Fin 2) (p : Site L) :
    p ≠ verticalMatching hL c p := by
  intro h
  exact coordinateMatching_ne hL c p.1 (congrArg Prod.fst h)

lemma horizontalMatching_symm {L : ℕ} (hL : Even L) (c : Fin 2) :
    (horizontalMatching hL c).symm = horizontalMatching hL c := by
  apply Equiv.ext
  intro p
  apply (horizontalMatching hL c).injective
  simp

lemma verticalMatching_symm {L : ℕ} (hL : Even L) (c : Fin 2) :
    (verticalMatching hL c).symm = verticalMatching hL c := by
  apply Equiv.ext
  intro p
  apply (verticalMatching hL c).injective
  simp

/-- Different coordinate directions commute for either choice of colors. -/
lemma horizontal_vertical_matching_commute {L : ℕ} (hL : Even L)
    (c d : Fin 2) (p : Site L) :
    horizontalMatching hL c (verticalMatching hL d p) =
      verticalMatching hL d (horizontalMatching hL c p) := rfl

end SquareTorus
