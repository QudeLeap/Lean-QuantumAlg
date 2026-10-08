/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Expansion
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Core.Base.Layout.Signature
public import QuantumAlg.Util.FiniteCyclicDLP
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation

/-!
# Parameters for known-order range preparation

This module defines the reviewed endpoint width, canonical gap arithmetic and
resource formulas shared by the finite-cyclic DLP construction.  The actual
native word and its complete semantics live in `Order.Preparation.Native`.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderPreparation

noncomputable section

open scoped BigOperators

universe u

variable {G : Type u} [Group G]

/-- The reviewed exponent-register width used by the finite-cyclic endpoint. -/
@[expose, implicit_reducible] public def width (P : KnownOrderProblem G) : Nat :=
  FiniteCyclicDLP.orderWidth P

/-- The known order fits in its reviewed exponent register. -/
public theorem order_le_capacity (P : KnownOrderProblem G) :
    P.order ≤ 2 ^ width P := by
  calc
    P.order ≤ 12 * P.order := by omega
    _ ≤ 2 ^ width P := by
      exact Nat.le_pow_clog (by norm_num : 1 < 2) (12 * P.order)

/-- The twelvefold margin makes the order strictly smaller than the register capacity. -/
public theorem order_lt_capacity (P : KnownOrderProblem G) :
    P.order < 2 ^ width P := by
  calc
    P.order < 12 * P.order := by
      have := Nat.pos_of_ne_zero P.order_ne_zero
      omega
    _ ≤ 2 ^ width P := by
      exact Nat.le_pow_clog (by norm_num : 1 < 2) (12 * P.order)

/-- Canonical physical qubits for one exponent register. -/
public abbrev layout (P : KnownOrderProblem G) : QuantumLayout (width P) :=
  (QuantumSignature.qubits (width P)).canonicalPlacement.layout

/-- Every exponent in a certified expansion contributes no more than the full sum. -/
private theorem power_le_order (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (index : Fin expansion.count) :
    2 ^ expansion.ell index ≤ P.order := by
  calc
    2 ^ expansion.ell index ≤ ∑ current, 2 ^ expansion.ell current :=
      Finset.single_le_sum
        (f := fun current : Fin expansion.count => 2 ^ expansion.ell current)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
    _ = P.order := expansion.sum_powers.symm

/-- Every set-bit exponent fits strictly inside the reviewed register. -/
public theorem ell_lt_width (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (index : Fin expansion.count) :
    expansion.ell index < width P := by
  have powers : 2 ^ expansion.ell index < 2 ^ width P :=
    lt_of_le_of_lt (power_le_order P expansion index) (order_lt_capacity P)
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp powers

/-- Index before one gap in the increasing set-bit sequence. -/
@[expose] public def leftIndex {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) : Fin expansion.count :=
  ⟨gap.val, by
    have gapBound := gap.isLt
    have positive := expansion.count_pos
    unfold OrderExpansion.gaps at gapBound
    omega⟩

/-- Index after one gap in the increasing set-bit sequence. -/
@[expose] public def rightIndex {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) : Fin expansion.count :=
  ⟨gap.val + 1, by
    have gapBound := gap.isLt
    have positive := expansion.count_pos
    unfold OrderExpansion.gaps at gapBound
    omega⟩

/-- The right set bit is strictly above the left set bit of every gap. -/
public theorem ell_left_lt_right {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) :
    expansion.ell (leftIndex expansion gap) <
      expansion.ell (rightIndex expansion gap) := by
  apply expansion.ell_strict
  change gap.val < gap.val + 1
  omega

/-- Number of logical bit positions opened by one strict binary gap. -/
public def gapWidth {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) : Nat :=
  expansion.ell (rightIndex expansion gap) -
    expansion.ell (leftIndex expansion gap)

/-- Mass of all set bits strictly preceding one gap. -/
@[expose] public def prefixMass {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) : Nat :=
  ∑ index : Fin expansion.count,
    if index.val < gap.val then 2 ^ expansion.ell index else 0

/-- Source rotation angle for one Shukla--Vedula gap. -/
@[expose] public def sourceAngle {N : Nat} (expansion : OrderExpansion N)
    (gap : Fin expansion.gaps) : Real :=
  -2 * Real.arccos
    (Real.sqrt
      (((2 ^ expansion.ell (leftIndex expansion gap) : Nat) : Real) /
        ((N - prefixMass expansion gap : Nat) : Real)))

/-- Exact number of native one-qubit instructions in the actual preparation word. -/
public def singleQubitCount {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.gaps + expansion.first +
    ∑ gap : Fin expansion.gaps, ((if gap.val = 0 then 1 else 4) +
      4 * gapWidth expansion gap)

/-- Exact number of native CNOT instructions in the actual preparation word. -/
public def cnotCount {N : Nat} (expansion : OrderExpansion N) : Nat :=
  ∑ gap : Fin expansion.gaps, ((if gap.val = 0 then 0 else 2) +
    gapWidth expansion gap)

/-- Exact unit-duration dependency depth of the actual preparation word. -/
@[expose] public def unitDepth {N : Nat} (expansion : OrderExpansion N) : Nat :=
  expansion.gaps + (if expansion.first = 0 then 0 else 1) +
    ∑ gap : Fin expansion.gaps, ((if gap.val = 0 then 1 else 5) +
      3 * gapWidth expansion gap)


end

end QuantumAlg.FiniteCyclicDLP.OrderPreparation
