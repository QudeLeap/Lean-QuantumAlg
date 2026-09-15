/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Source.Exact
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Representation.Readout

/-!
# The actual source basis under its original integer interpretation

The source j words, one, and the lattice modulus lie strictly below the
positive signed boundary of the original recovery width. The existing
signed interpretation therefore returns their exact source integers from
the actual loaded cells. Every capacity and initialization fact is derived
internally from the original width formula and real lexical allocation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

private theorem basis_of_rows (ctx : RuntimeCtx kind) (width : Nat)
    (store : Store (BasisLayout.context ctx width)) (value : NumberTheory.IntegerBasis3)
    (first : BasisLayout.integerRow (BasisLayout.firstRow ctx width) store = value.first)
    (second : BasisLayout.integerRow (BasisLayout.secondRow ctx width) store = value.second)
    (third : BasisLayout.integerRow (BasisLayout.thirdRow ctx width) store = value.third) :
    BasisLayout.integerBasis ctx width store = value := by
  cases value
  change NumberTheory.IntegerBasis3.mk _ _ _ = _
  rw [first, second, third]

/-- Original-width native loading realizes the exact integer source basis and zero target. -/
theorem nativeLattice_basis_initialization_integer_source (N m ell : Nat)
    (first second : CInputRef ctx (.unsignedWord (ell + m))) (store : Store ctx) :
    let width := RSA.ShortLogWidths.coordinateWidth N m ell
    let result := storeStep first second width (ell + m) (BasisLayout.pushStore width store)
    BasisLayout.integerBasis ctx width result =
        { first := ((store.read first).toNat, (store.read second).toNat, 1)
          second := ((2 ^ (ell + m) : Nat), 0, 0)
          third := (0, (2 ^ (ell + m) : Nat), 0) } ∧
      BasisLayout.integerRow (BasisLayout.target ctx width) result = (0, 0, 0) := by
  let width := RSA.ShortLogWidths.coordinateWidth N m ell
  let result : Store (BasisLayout.context ctx width) :=
    storeStep first second width (ell + m) (BasisLayout.pushStore width store)
  have positive : 0 < width := RSA.ShortLogWidths.coordinateWidth_pos N m ell
  have periodFits : 2 ^ (ell + m) < 2 ^ (width - 1) :=
    RSA.ShortLogWidths.shortLog_sourceModulus_lt_signedCapacity N m ell
  have firstFits : (store.read first).toNat < 2 ^ (width - 1) :=
    (store.read first).toNat_lt.trans periodFits
  have secondFits : (store.read second).toNat < 2 ^ (width - 1) :=
    (store.read second).toNat_lt.trans periodFits
  have oneFits : 1 < 2 ^ (width - 1) :=
    (Nat.succ_le_iff.mpr (Nat.two_pow_pos (ell + m))).trans_lt periodFits
  have zeroFits : 0 < 2 ^ (width - 1) := Nat.two_pow_pos (width - 1)
  have actual := nativeLattice_basis_initialization_exact_source N m ell first second store
  have firstInteger := BasisLayout.nativeLattice_integer_row_of_nonnegative
    (BasisLayout.firstRow ctx width) result (store.read first).toNat (store.read second).toNat 1
    actual.1 positive firstFits secondFits oneFits
  have secondInteger := BasisLayout.nativeLattice_integer_row_of_nonnegative
    (BasisLayout.secondRow ctx width) result (2 ^ (ell + m)) 0 0
    actual.2.1 positive periodFits zeroFits zeroFits
  have thirdInteger := BasisLayout.nativeLattice_integer_row_of_nonnegative
    (BasisLayout.thirdRow ctx width) result 0 (2 ^ (ell + m)) 0
    actual.2.2.1 positive zeroFits periodFits zeroFits
  have targetInteger := BasisLayout.nativeLattice_integer_row_of_nonnegative
    (BasisLayout.target ctx width) result 0 0 0
    actual.2.2.2 positive zeroFits zeroFits zeroFits
  refine ⟨?_, targetInteger⟩
  exact basis_of_rows ctx width result
    { first := ((store.read first).toNat, (store.read second).toNat, 1)
      second := ((2 ^ (ell + m) : Nat), 0, 0)
      third := (0, (2 ^ (ell + m) : Nat), 0) }
    firstInteger secondInteger thirdInteger

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
