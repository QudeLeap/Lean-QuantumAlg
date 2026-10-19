/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.OfFn

/-!
# Canonical binary expansion of a positive finite-cyclic order

The order is executable input data, so the finite-cyclic DLP endpoint derives
its increasing set-bit sequence from `Nat.bitIndices`.  A caller does not
supply a second expansion certificate.  The same structure includes one-term
expansions, hence powers of two and `N = 1`.
-/

namespace QuantumAlg.FiniteCyclicDLP

open scoped BigOperators

/-- Strictly increasing set-bit exponents of a positive natural number. -/
public structure OrderExpansion (N : Nat) where
  /-- Number of nonzero binary digits. -/
  count : Nat
  /-- A positive order has at least one nonzero binary digit. -/
  count_pos : 0 < count
  /-- Nonzero digit positions in increasing order. -/
  ell : Fin count → Nat
  /-- Binary digit positions do not repeat. -/
  ell_strict : StrictMono ell
  /-- Reassembling the selected powers of two gives the order. -/
  sum_powers : N = ∑ index, 2 ^ ell index

namespace OrderExpansion

/-- The canonical expansion computed from the known order itself. -/
public def canonical (N : Nat) (positive : 0 < N) : OrderExpansion N where
  count := N.bitIndices.length
  count_pos := by
    apply List.length_pos_iff.mpr
    intro empty
    have reconstructed := Nat.sum_map_two_pow_bitIndices N
    rw [empty] at reconstructed
    simp only [List.map_nil, List.sum_nil] at reconstructed
    omega
  ell := N.bitIndices.get
  ell_strict := Nat.bitIndices_sorted.strictMono_get
  sum_powers := by
    calc
      N = (N.bitIndices.map (fun index => 2 ^ index)).sum :=
        (Nat.sum_map_two_pow_bitIndices N).symm
      _ = (List.ofFn fun index : Fin N.bitIndices.length =>
          2 ^ N.bitIndices.get index).sum := by
        congr 1
        symm
        calc
          List.ofFn (fun index : Fin N.bitIndices.length =>
              2 ^ N.bitIndices.get index) =
              (List.ofFn N.bitIndices.get).map (fun index => 2 ^ index) :=
            List.ofFn_comp' N.bitIndices.get (fun index => 2 ^ index)
          _ = N.bitIndices.map (fun index => 2 ^ index) := by
            rw [List.ofFn_get]
      _ = ∑ index : Fin N.bitIndices.length, 2 ^ N.bitIndices.get index := by
        rw [List.sum_ofFn]

/-- Number of gaps between successive set bits. -/
@[expose] public def gaps {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.count - 1

/-- Lowest set-bit exponent. -/
@[expose, implicit_reducible] public def first {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.ell ⟨0, expansion.count_pos⟩

/-- Highest set-bit exponent. -/
@[expose, implicit_reducible] public def last {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.ell ⟨expansion.count - 1, by
    have := expansion.count_pos
    omega⟩

/-- The one-qubit envelope of the literal Shukla--Vedula preparation. -/
public def singleQubitBound {N : Nat} (expansion : OrderExpansion N) : Nat :=
  5 * expansion.gaps + 6 * expansion.last - 5 * expansion.first

/-- The CNOT envelope of the literal Shukla--Vedula preparation. -/
public def cnotBound {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.last - expansion.first + 2 * expansion.gaps

/-- The sequential unit-duration envelope of that preparation. -/
public def depthBound {N : Nat} (expansion : OrderExpansion N) : Nat :=
  5 * (expansion.last - expansion.first) + 5 * expansion.gaps + 1

/-- A one-bit expansion represents exactly its sole power of two. -/
public lemma eq_pow_first_of_count_eq_one {N : Nat} (expansion : OrderExpansion N)
    (single : expansion.count = 1) :
    N = 2 ^ expansion.first := by
  cases expansion with
  | mk count count_pos ell ell_strict sum_powers =>
      dsimp at single ⊢
      subst count
      simpa [OrderExpansion.first] using sum_powers

/-- `N = 1` is represented by the single exponent zero. -/
@[simp] public lemma canonical_one_count : (canonical 1 (by decide)).count = 1 := by
  rfl

@[simp] public lemma canonical_one_first : (canonical 1 (by decide)).first = 0 := by
  rfl

/-- A canonical order expansion viewed as a nontrivial sequence of binary
gaps.  This view is derived from executable order data; callers never supply
it as an independent certificate. -/
public structure PositiveGapExpansion (N : Nat) where
  /-- Number of gaps between successive set bits. -/
  gaps : Nat
  /-- A nontrivial expansion has at least one gap. -/
  gaps_pos : 1 ≤ gaps
  /-- Set-bit exponents, in increasing order. -/
  ell : Fin (gaps + 1) → Nat
  /-- Binary digit positions do not repeat. -/
  ell_strict : StrictMono ell
  /-- Reassembling the selected powers of two gives the order. -/
  sum_powers : N = ∑ index, 2 ^ ell index
  /-- Positivity is retained for the normalized range state. -/
  positive : 0 < N

/-- A nontrivial expansion has exactly one more set bit than gaps. -/
public lemma gaps_add_one_eq_count {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) :
    expansion.gaps + 1 = expansion.count := by
  unfold gaps
  omega

/-- Canonical reindexing from gap-oriented indices to the original set-bit
indices. -/
public def gapEquiv {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) :
    Fin (expansion.gaps + 1) ≃ Fin expansion.count :=
  finCongr (gaps_add_one_eq_count expansion multiple)

/-- Derive the positive-gap view of a nontrivial canonical expansion. -/
@[expose] public def toPositiveGapExpansion {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N) :
    PositiveGapExpansion N where
  gaps := expansion.gaps
  gaps_pos := by
    unfold gaps
    omega
  ell := fun index => expansion.ell (gapEquiv expansion multiple index)
  ell_strict := by
    intro left right less
    apply expansion.ell_strict
    simpa [gapEquiv] using less
  sum_powers := by
    calc
      N = ∑ index : Fin expansion.count, 2 ^ expansion.ell index :=
        expansion.sum_powers
      _ = ∑ index : Fin (expansion.gaps + 1),
          2 ^ expansion.ell (gapEquiv expansion multiple index) :=
        ((gapEquiv expansion multiple).sum_comp
          (fun index : Fin expansion.count => 2 ^ expansion.ell index)).symm
  positive := positive

namespace PositiveGapExpansion

variable {N : Nat}

/-- Repackage the positive-gap view as its equivalent ordinary expansion.
The endpoint still derives both views from the same canonical input data. -/
@[expose, implicit_reducible]
public def asOrderExpansion (expansion : PositiveGapExpansion N) : OrderExpansion N where
  count := expansion.gaps + 1
  count_pos := by omega
  ell := expansion.ell
  ell_strict := expansion.ell_strict
  sum_powers := expansion.sum_powers

@[simp] public lemma asOrderExpansion_count (expansion : PositiveGapExpansion N) :
    expansion.asOrderExpansion.count = expansion.gaps + 1 := rfl

@[simp] public lemma asOrderExpansion_gaps (expansion : PositiveGapExpansion N) :
    expansion.asOrderExpansion.gaps = expansion.gaps := by
  change (expansion.gaps + 1) - 1 = expansion.gaps
  omega

@[simp] public lemma asOrderExpansion_ell (expansion : PositiveGapExpansion N)
    (index : Fin (expansion.gaps + 1)) :
    expansion.asOrderExpansion.ell index = expansion.ell index := rfl

/-- Lowest set-bit exponent in the nontrivial expansion. -/
@[expose, implicit_reducible] public def first (expansion : PositiveGapExpansion N) : Nat :=
  expansion.ell 0

@[simp] public lemma asOrderExpansion_first (expansion : PositiveGapExpansion N) :
    expansion.asOrderExpansion.first = expansion.first := rfl

/-- Highest set-bit exponent in the nontrivial expansion. -/
@[expose, implicit_reducible] public def last (expansion : PositiveGapExpansion N) : Nat :=
  expansion.ell (Fin.last expansion.gaps)

@[simp] public lemma asOrderExpansion_last (expansion : PositiveGapExpansion N) :
    expansion.asOrderExpansion.last = expansion.last := by
  unfold OrderExpansion.last asOrderExpansion last
  congr 1

/-- Converting a nontrivial ordinary expansion to the gap view and back
recovers the original expansion, including its executable exponent map. -/
public lemma asOrderExpansion_toPositiveGapExpansion
    (expansion : OrderExpansion N) (multiple : 2 ≤ expansion.count)
    (positive : 0 < N) :
    (expansion.toPositiveGapExpansion multiple positive).asOrderExpansion =
      expansion := by
  cases expansion with
  | mk count countPositive ell strict sum =>
      cases count with
      | zero => omega
      | succ count =>
          cases count with
          | zero =>
              change 2 ≤ 1 at multiple
              omega
          | succ count => rfl

/-- Intrinsic register width of the nontrivial expansion. -/
@[expose, implicit_reducible] public def width (expansion : PositiveGapExpansion N) : Nat :=
  expansion.last + 1

/-- The represented order fits in its intrinsic highest-bit width. -/
@[expose] public def fits (expansion : PositiveGapExpansion N) : Prop :=
  N ≤ 2 ^ expansion.width

/-- Strictly increasing set-bit positions prove the intrinsic-width bound. -/
public lemma fits_proof (expansion : PositiveGapExpansion N) :
    expansion.fits := by
  classical
  unfold fits
  calc
    N = ∑ index, 2 ^ expansion.ell index := expansion.sum_powers
    _ = ∑ exponent ∈ Finset.univ.image expansion.ell, 2 ^ exponent := by
      rw [Finset.sum_image]
      exact expansion.ell_strict.injective.injOn
    _ ≤ 2 ^ expansion.width :=
      (Nat.geomSum_lt (m := 2) (s := Finset.univ.image expansion.ell)
        (n := expansion.width) (by omega) (by
          intro exponent member
          rcases Finset.mem_image.mp member with ⟨index, -, rfl⟩
          unfold width last
          have upper : expansion.ell index ≤
              expansion.ell (Fin.last expansion.gaps) :=
            expansion.ell_strict.monotone (Fin.le_last index)
          omega)).le

end PositiveGapExpansion

end OrderExpansion

end QuantumAlg.FiniteCyclicDLP
