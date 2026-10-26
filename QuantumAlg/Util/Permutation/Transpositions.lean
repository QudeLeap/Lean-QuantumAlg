/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.Permutation.SwapFactors

/-! # Actual ordered transposition coordinates of a fixed finite permutation -/

namespace QuantumAlg.Permutation

noncomputable section

/-- Two distinct static coordinates, rather than an unevaluated permutation oracle. -/
structure Transposition (α : Type*) where
  first : α
  second : α
  different : first ≠ second

namespace Transposition

/-- The permutation exchanges exactly the two supplied coordinates. -/
def permutation {α : Type*} [DecidableEq α] (exchange : Transposition α) : Equiv.Perm α :=
  Equiv.swap exchange.first exchange.second

/-- Extract static target positions from a certified transposition. -/
def ofIsSwap {α : Type*} [DecidableEq α] (value : Equiv.Perm α)
    (certificate : value.IsSwap) : Transposition α where
  first := certificate.choose
  second := certificate.choose_spec.choose
  different := certificate.choose_spec.choose_spec.1

/-- Extracting the two positions keeps the complete original permutation. -/
lemma ofIsSwap_permutation {α : Type*} [DecidableEq α] (value : Equiv.Perm α)
    (certificate : value.IsSwap) :
    (ofIsSwap value certificate).permutation = value :=
  certificate.choose_spec.choose_spec.2.symm

end Transposition

/-- The actual static factor list, in the same order as its certified product. -/
def transpositions {α : Type*} [Fintype α] [LinearOrder α]
    (value : Equiv.Perm α) : List (Transposition α) :=
  (Equiv.Perm.swapFactors value).val.attach.map (fun factor =>
    Transposition.ofIsSwap factor.val ((Equiv.Perm.swapFactors value).property.2 _ factor.property))

/-- Coordinate extraction preserves every factor and its original order. -/
lemma transpositions_map {α : Type*} [Fintype α] [LinearOrder α]
    (value : Equiv.Perm α) :
    (transpositions value).map Transposition.permutation = (Equiv.Perm.swapFactors value).val := by
  simp [transpositions, List.map_map, Transposition.ofIsSwap_permutation]

/-- The ordered coordinate product is exactly the requested finite permutation. -/
lemma transpositions_product {α : Type*} [Fintype α] [LinearOrder α]
    (value : Equiv.Perm α) :
    ((transpositions value).map Transposition.permutation).prod = value := by
  rw [transpositions_map]
  exact (Equiv.Perm.swapFactors value).property.1

/-- A fixed barrel permutation uses at most one transposition per carrier coordinate. -/
lemma transpositions_length_le {α : Type*} [Fintype α] [LinearOrder α]
    (value : Equiv.Perm α) : (transpositions value).length ≤ Fintype.card α := by
  simpa only [transpositions, List.length_map, List.length_attach] using
    swapFactors_length_le value

end

end QuantumAlg.Permutation
