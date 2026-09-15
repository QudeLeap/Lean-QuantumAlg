/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Store
import all QuantumAlg.Components.Classical.Word
import all QuantumAlg.Util.Classical.NumberTheory.Basic
import all QuantumAlg.Util.NumberTheory.LatticeReduction

/-!
# Integer observations of the actual lattice coordinate cells

The three values of a row are read separately from their actual storage
references and interpreted by the existing two's-complement word semantics.
The ordered source basis below is a mathematical observation of nine cells;
no vector-valued runtime cell or additional instruction is introduced.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout

open Execution
open ClassicalAlgorithms.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Interpret each actual coordinate of one row with the shared signed-word semantics. -/
def integerRow (row : FirstRow.Refs ctx width) (store : Store ctx) :
    NumberTheory.IntegerPoint3 :=
  ((BoundedSigned.decode (ClassicalRoutines.decodeWord
      (store.read (.storage row.first.toCStorageRef)))).toInt,
    (BoundedSigned.decode (ClassicalRoutines.decodeWord
      (store.read (.storage row.second.toCStorageRef)))).toInt,
    (BoundedSigned.decode (ClassicalRoutines.decodeWord
      (store.read (.storage row.third.toCStorageRef)))).toInt)

/-- The ordered integer basis is the observation of the three actual basis rows. -/
def integerBasis (ctx : RuntimeCtx kind) (width : Nat) (store : Store (context ctx width)) :
    NumberTheory.IntegerBasis3 where
  first := integerRow (firstRow ctx width) store
  second := integerRow (secondRow ctx width) store
  third := integerRow (thirdRow ctx width) store

private theorem signed_word_of_nonnegative (word : CShape.Word width)
    (positive : 0 < width) (fits : word.toNat < 2 ^ (width - 1)) :
    (BoundedSigned.decode (ClassicalRoutines.decodeWord word)).toInt =
      (word.toNat : Int) := by
  have power : 2 ^ width = 2 * 2 ^ (width - 1) := by
    calc
      2 ^ width = 2 ^ ((width - 1) + 1) :=
        congrArg (fun exponent : Nat => 2 ^ exponent)
          (Nat.sub_add_cancel (Nat.succ_le_of_lt positive)).symm
      _ = 2 * 2 ^ (width - 1) := by rw [pow_succ, Nat.mul_comm]
  have payload : (BitVec.ofFin (ClassicalRoutines.decodeWord word)).toNat =
      word.toNat := by
    cases word
    rfl
  have below : 2 * (BitVec.ofFin (ClassicalRoutines.decodeWord word)).toNat <
      2 ^ width := by
    rw [payload, power]
    exact Nat.mul_lt_mul_of_pos_left fits (by decide)
  exact (BitVec.toInt_eq_toNat_of_lt below).trans (congrArg (fun value : Nat => (value : Int))
    payload)

/-- Actual nonnegative row values below the sign boundary have those exact integer values. -/
theorem nativeLattice_integer_row_of_nonnegative (row : FirstRow.Refs ctx width)
    (store : Store ctx) (first second third : Nat)
    (values : rowValues row store = (first, second, third))
    (positive : 0 < width)
    (firstFits : first < 2 ^ (width - 1))
    (secondFits : second < 2 ^ (width - 1))
    (thirdFits : third < 2 ^ (width - 1)) :
    integerRow row store = ((first : Int), (second : Int), (third : Int)) := by
  have firstValue : (store.read (.storage row.first.toCStorageRef)).toNat = first :=
    congrArg (fun value : Nat × Nat × Nat => value.1) values
  have secondValue : (store.read (.storage row.second.toCStorageRef)).toNat = second :=
    congrArg (fun value : Nat × Nat × Nat => value.2.1) values
  have thirdValue : (store.read (.storage row.third.toCStorageRef)).toNat = third :=
    congrArg (fun value : Nat × Nat × Nat => value.2.2) values
  have firstBound : (store.read (.storage row.first.toCStorageRef)).toNat <
      2 ^ (width - 1) := lt_of_eq_of_lt firstValue firstFits
  have secondBound : (store.read (.storage row.second.toCStorageRef)).toNat <
      2 ^ (width - 1) := lt_of_eq_of_lt secondValue secondFits
  have thirdBound : (store.read (.storage row.third.toCStorageRef)).toNat <
      2 ^ (width - 1) := lt_of_eq_of_lt thirdValue thirdFits
  exact Prod.ext
    ((signed_word_of_nonnegative _ positive firstBound).trans
      (congrArg (fun value : Nat => (value : Int)) firstValue))
    (Prod.ext ((signed_word_of_nonnegative _ positive secondBound).trans
      (congrArg (fun value : Nat => (value : Int)) secondValue))
      ((signed_word_of_nonnegative _ positive thirdBound).trans
        (congrArg (fun value : Nat => (value : Int)) thirdValue)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout
