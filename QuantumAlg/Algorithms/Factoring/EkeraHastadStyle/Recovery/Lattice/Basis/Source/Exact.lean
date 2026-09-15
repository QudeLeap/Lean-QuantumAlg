/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Source
import all QuantumAlg.Util.RSA.ShortLog.WidthBounds

/-!
# Exact source coordinates at the original recovery width

The same original uniform word width is supplied to the actual row layout
and loading instructions. Its proved capacity contains both decoded j words,
one, and the full lattice modulus. Consequently every stored initial basis
coordinate equals its original source integer without truncation. The target
still has its three actual zero values before its separate native loading.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- The actual original-width loading stores all original source coordinates exactly. -/
theorem nativeLattice_basis_initialization_exact_source (N m ell : Nat)
    (first second : CInputRef ctx (.unsignedWord (ell + m))) (store : Store ctx) :
    let width := RSA.ShortLogWidths.coordinateWidth N m ell
    let result := storeStep first second width (ell + m) (BasisLayout.pushStore width store)
    BasisLayout.rowValues (BasisLayout.firstRow ctx width) result =
        ((store.read first).toNat, (store.read second).toNat, 1) ∧
      BasisLayout.rowValues (BasisLayout.secondRow ctx width) result =
        (2 ^ (ell + m), 0, 0) ∧
      BasisLayout.rowValues (BasisLayout.thirdRow ctx width) result =
        (0, 2 ^ (ell + m), 0) ∧
      BasisLayout.rowValues (BasisLayout.target ctx width) result = (0, 0, 0) := by
  let width := RSA.ShortLogWidths.coordinateWidth N m ell
  have capacity : 2 ^ (ell + m) < 2 ^ width :=
    RSA.ShortLogWidths.shortLog_sourceModulus_lt_coordinateCapacity N m ell
  have firstBound : (store.read first).toNat < 2 ^ width :=
    (store.read first).toNat_lt.trans capacity
  have secondBound : (store.read second).toNat < 2 ^ width :=
    (store.read second).toNat_lt.trans capacity
  have oneBound : 1 < 2 ^ width :=
    (Nat.succ_le_iff.mpr (Nat.two_pow_pos (ell + m))).trans_lt capacity
  have actual := nativeLattice_basis_initialization_source first second width (ell + m) store
  simpa only [Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt secondBound,
    Nat.mod_eq_of_lt oneBound, Nat.mod_eq_of_lt capacity] using actual

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
