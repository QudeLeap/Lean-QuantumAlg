/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Arithmetic
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Expansion

/-!
# Canonical expansion bridge for preparation arithmetic

The executable order expansion and its derived positive-gap view use the same
set-bit sequence.  These lemmas identify the gap indices, prefix masses, and
rotation angles used by the native circuit with the arithmetic development.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation

noncomputable section

open scoped BigOperators

/-- The derived view retains the canonical number of binary gaps. -/
@[simp] public lemma positiveGap_gaps {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N) :
    (expansion.toPositiveGapExpansion multiple positive).gaps = expansion.gaps := rfl

/-- The derived view retains the lowest set-bit exponent. -/
public lemma positiveGap_first {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N) :
    (expansion.toPositiveGapExpansion multiple positive).first = expansion.first := by
  change expansion.ell (expansion.gapEquiv multiple 0) =
    expansion.ell ⟨0, expansion.count_pos⟩
  congr 1

/-- The derived view retains the highest set-bit exponent. -/
public lemma positiveGap_last {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N) :
    (expansion.toPositiveGapExpansion multiple positive).last = expansion.last := by
  change expansion.ell
      (expansion.gapEquiv multiple (Fin.last expansion.gaps)) =
    expansion.ell ⟨expansion.count - 1, by omega⟩
  congr 1

/-- The intrinsic width of the derived view is the canonical active width. -/
public lemma positiveGap_width {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N) :
    (expansion.toPositiveGapExpansion multiple positive).width =
      expansion.last + 1 := by
  unfold OrderExpansion.PositiveGapExpansion.width
  rw [positiveGap_last expansion multiple positive]

/-- The left endpoint of a canonical gap is its gap-oriented predecessor. -/
public lemma positiveGap_ell_left {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N)
    (gap : Fin expansion.gaps) :
    (expansion.toPositiveGapExpansion multiple positive).ell gap.castSucc =
      expansion.ell (leftIndex expansion gap) := by
  change expansion.ell (expansion.gapEquiv multiple gap.castSucc) = _
  congr 1

/-- The right endpoint of a canonical gap is its gap-oriented successor. -/
public lemma positiveGap_ell_right {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N)
    (gap : Fin expansion.gaps) :
    (expansion.toPositiveGapExpansion multiple positive).ell gap.succ =
      expansion.ell (rightIndex expansion gap) := by
  change expansion.ell (expansion.gapEquiv multiple gap.succ) = _
  congr 1

/-- Reindexing the derived positive-gap prefix recovers the prefix mass used
by the native schedule. -/
public lemma positiveGap_prefixMass {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N)
    (gap : Fin expansion.gaps) :
    (expansion.toPositiveGapExpansion multiple positive).prefixMass gap =
      prefixMass expansion gap := by
  let equivalence := expansion.gapEquiv multiple
  unfold OrderExpansion.PositiveGapExpansion.prefixMass prefixMass
  change (∑ index : Fin (expansion.gaps + 1),
      if index.val < gap.val then
        2 ^ expansion.ell (equivalence index) else 0) =
    ∑ index : Fin expansion.count,
      if index.val < gap.val then 2 ^ expansion.ell index else 0
  simpa [equivalence, OrderExpansion.gapEquiv] using
    equivalence.sum_comp (fun index : Fin expansion.count =>
      if index.val < gap.val then 2 ^ expansion.ell index else 0)

/-- The arithmetic source ratio is exactly the ratio used to construct the
native circuit's rotation angle. -/
public lemma positiveGap_sourceRatio {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N)
    (gap : Fin expansion.gaps) :
    (expansion.toPositiveGapExpansion multiple positive).sourceRatio gap =
      ((2 ^ expansion.ell (leftIndex expansion gap) : Nat) : Real) /
        ((N - prefixMass expansion gap : Nat) : Real) := by
  have ellEquality :
      expansion.ell (expansion.gapEquiv multiple gap.castSucc) =
        expansion.ell (leftIndex expansion gap) := by
    exact positiveGap_ell_left expansion multiple positive gap
  unfold OrderExpansion.PositiveGapExpansion.sourceRatio
  change
    ((2 ^ expansion.ell (expansion.gapEquiv multiple gap.castSucc) : Nat) : Real) /
        ((N - (expansion.toPositiveGapExpansion multiple positive).prefixMass gap : Nat) :
          Real) = _
  rw [ellEquality,
    positiveGap_prefixMass expansion multiple positive gap]

/-- The rotation angle proved by the positive-gap arithmetic is the literal
angle used by the native preparation stage. -/
public lemma positiveGap_sourceAngle {N : Nat} (expansion : OrderExpansion N)
    (multiple : 2 ≤ expansion.count) (positive : 0 < N)
    (gap : Fin expansion.gaps) :
    (expansion.toPositiveGapExpansion multiple positive).sourceAngle gap =
      sourceAngle expansion gap := by
  unfold OrderExpansion.PositiveGapExpansion.sourceAngle sourceAngle
  rw [
    positiveGap_sourceRatio expansion multiple positive gap]

end


end QuantumAlg.FiniteCyclicDLP.OrderPreparation
