/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Store

/-!
# Intrinsic separation of all actual lattice coordinates

All twelve coordinate keys belong to the actual nested row contexts. Their
uniqueness and separation from original inputs follow from that context's
existing key certificate. Finite indices below refer to the actual reverse
allocation order, so local arithmetic and loading can discharge positional
conditions without requiring caller-supplied fresh or distinct storage.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The twelve real coordinate keys, in actual target-to-first-row stack order. -/
def internalKeys (ctx : RuntimeCtx kind) (width : Nat) : List StorageKey :=
  RowLayout.internalKeys (context3 ctx width) width ++
    (RowLayout.internalKeys (context2 ctx width) width ++
      (RowLayout.internalKeys (context1 ctx width) width ++ RowLayout.internalKeys ctx width))

/-- These are exactly the keys added to the original context by the actual four row scopes. -/
theorem nativeLattice_basis_keys (ctx : RuntimeCtx kind) (width : Nat) :
    (context ctx width).keys = internalKeys ctx width ++ ctx.keys := by
  have first := RowLayout.nativeLattice_row_keys ctx width
  have second := RowLayout.nativeLattice_row_keys (context1 ctx width) width
  have third := RowLayout.nativeLattice_row_keys (context2 ctx width) width
  have target := RowLayout.nativeLattice_row_keys (context3 ctx width) width
  have combined := target.trans (congrArg
    (fun keys => RowLayout.internalKeys (context3 ctx width) width ++ keys)
    (third.trans (congrArg
      (fun keys => RowLayout.internalKeys (context2 ctx width) width ++ keys)
      (second.trans (congrArg
        (fun keys => RowLayout.internalKeys (context1 ctx width) width ++ keys) first)))))
  exact combined.trans (by simp only [internalKeys, List.append_assoc])

/-- Intrinsic key uniqueness separates every one of the twelve actual coordinate destinations. -/
theorem nativeLattice_basis_nodup (ctx : RuntimeCtx kind) (width : Nat) :
    (internalKeys ctx width).Nodup := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeLattice_basis_keys] at unique
  exact (List.nodup_append.mp unique).1

/-- Every actual coordinate destination is fresh relative to all original storage entries. -/
theorem nativeLattice_basis_disjoint (ctx : RuntimeCtx kind) (width : Nat) :
    List.Disjoint (internalKeys ctx width) ctx.keys := by
  have unique := (context ctx width).keysNodup
  change (context ctx width).keys.Nodup at unique
  rw [nativeLattice_basis_keys] at unique
  apply List.disjoint_left.mpr
  intro key internal external
  exact (List.nodup_append.mp unique).2.2 key internal key external rfl

/-- The indexed key is an actual coordinate, with index zero at the newest target cell. -/
def cellKey (ctx : RuntimeCtx kind) (width : Nat) (index : Fin 12) : StorageKey :=
  (internalKeys ctx width).get ⟨index.val, by change index.val < 12; exact index.isLt⟩

/-- Different actual coordinate positions have different intrinsic storage identities. -/
theorem nativeLattice_basis_key_ne (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 12) (different : left ≠ right) :
    cellKey ctx width left ≠ cellKey ctx width right := by
  intro same
  have positions := (nativeLattice_basis_nodup ctx width).injective_get same
  exact different (Fin.ext (congrArg Fin.val positions))

/-- Original structural sources avoid every actual basis and target destination. -/
theorem nativeLattice_basis_source_free {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (index : Fin 12) :
    cellKey ctx width index ∉ (underRead input width).storageKeys := by
  rw [nativeLattice_basis_underRead_keys]
  intro present
  exact List.disjoint_left.mp (nativeLattice_basis_disjoint ctx width)
    (List.get_mem (internalKeys ctx width) _)
    (input.storageKeys_subset_context present)

/-- All first-row loader separation conditions are intrinsic facts of this actual layout. -/
theorem nativeLattice_basis_first_separated (ctx : RuntimeCtx kind) (width : Nat) :
    (firstRow ctx width).first.key ≠ (firstRow ctx width).second.key ∧
      (firstRow ctx width).first.key ≠ (firstRow ctx width).third.key ∧
      (firstRow ctx width).second.key ≠ (firstRow ctx width).third.key :=
  ⟨nativeLattice_basis_key_ne ctx width 11 10 (by decide),
    nativeLattice_basis_key_ne ctx width 11 9 (by decide),
    nativeLattice_basis_key_ne ctx width 10 9 (by decide)⟩

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout
