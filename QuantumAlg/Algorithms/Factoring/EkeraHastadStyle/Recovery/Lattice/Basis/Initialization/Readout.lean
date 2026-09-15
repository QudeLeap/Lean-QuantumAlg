/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Initialization
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Separation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.FirstRow.Readout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Constants.PowerOfTwo.Readout

/-!
# Actual five written values of initial basis loading

The actual first-row writes and two power-of-two loops use the twelve real
layout coordinates. All positional conditions are discharged by the actual
context's unique keys. The equations allow every incoming value in the work
layout; fresh allocation supplies the specific zero values separately. The
four remaining basis coordinates and all target coordinates are preserved.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth : Nat}

private theorem key_free (ctx : RuntimeCtx kind) (width : Nat)
    (left right : Fin 12) (different : left ≠ right) :
    BasisLayout.cellKey ctx width left ∉ [BasisLayout.cellKey ctx width right] := by
  simpa only [List.mem_singleton] using
    BasisLayout.nativeLattice_basis_key_ne ctx width left right different

private theorem row_power_frame {ctx : RuntimeCtx kind} {width : Nat}
    (count : Nat) (output : CWriteRef ctx (.unsignedWord width))
    (row : FirstRow.Refs ctx width) (store : Store ctx)
    (firstFree : output.key ≠ row.first.key)
    (secondFree : output.key ≠ row.second.key)
    (thirdFree : output.key ≠ row.third.key) :
    BasisLayout.rowValues row (PowerOfTwo.storeStep count output store) =
      BasisLayout.rowValues row store := by
  have first := PowerOfTwo.nativeLattice_powerOfTwo_read_other count output
    (.storage row.first.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using firstFree) store
  have second := PowerOfTwo.nativeLattice_powerOfTwo_read_other count output
    (.storage row.second.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using secondFree) store
  have third := PowerOfTwo.nativeLattice_powerOfTwo_read_other count output
    (.storage row.third.toCStorageRef)
    (by simpa only [CInputRef.storageKeys, List.mem_singleton] using thirdFree) store
  exact Prod.ext (congrArg CShape.Value.toNat first)
    (Prod.ext (congrArg CShape.Value.toNat second) (congrArg CShape.Value.toNat third))

/-- The two later native power loads preserve the actual values written into the first row. -/
theorem nativeLattice_basis_initialization_first_row
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (store : Store (BasisLayout.context ctx width)) :
    BasisLayout.rowValues (BasisLayout.firstRow ctx width)
        (storeStep first second width count store) =
      ((store.read (BasisLayout.underRead first width)).toNat % 2 ^ width,
        (store.read (BasisLayout.underRead second width)).toNat % 2 ^ width,
        ((store.read (.storage (BasisLayout.firstRow ctx width).third.toCStorageRef)).toNat + 1) %
          2 ^ width) := by
  let firstResult := FirstRow.storeStep (BasisLayout.underRead first width)
    (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width) store
  let secondResult := PowerOfTwo.storeStep count (BasisLayout.secondRow ctx width).first firstResult
  have separate := BasisLayout.nativeLattice_basis_first_separated ctx width
  have actual := FirstRow.nativeLattice_firstRow_read
    (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width) separate.1 separate.2.1 separate.2.2
    (BasisLayout.nativeLattice_basis_source_free second width 11) store
  have firstRow : BasisLayout.rowValues (BasisLayout.firstRow ctx width) firstResult =
      ((store.read (BasisLayout.underRead first width)).toNat % 2 ^ width,
        (store.read (BasisLayout.underRead second width)).toNat % 2 ^ width,
        ((store.read (.storage (BasisLayout.firstRow ctx width).third.toCStorageRef)).toNat + 1) %
          2 ^ width) :=
    Prod.ext actual.1 (Prod.ext actual.2.1 actual.2.2)
  exact (row_power_frame count (BasisLayout.thirdRow ctx width).second
    (BasisLayout.firstRow ctx width) secondResult
    (BasisLayout.nativeLattice_basis_key_ne ctx width 4 11 (by decide))
    (BasisLayout.nativeLattice_basis_key_ne ctx width 4 10 (by decide))
    (BasisLayout.nativeLattice_basis_key_ne ctx width 4 9 (by decide))).trans
    ((row_power_frame count (BasisLayout.secondRow ctx width).first
      (BasisLayout.firstRow ctx width) firstResult
      (BasisLayout.nativeLattice_basis_key_ne ctx width 8 11 (by decide))
      (BasisLayout.nativeLattice_basis_key_ne ctx width 8 10 (by decide))
      (BasisLayout.nativeLattice_basis_key_ne ctx width 8 9 (by decide))).trans firstRow)

/-- The two actual power coordinates use their original values, without a zero-input premise. -/
theorem nativeLattice_basis_initialization_power_values
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (store : Store (BasisLayout.context ctx width)) :
    ((storeStep first second width count store).read
        (.storage (BasisLayout.secondRow ctx width).first.toCStorageRef)).toNat =
        (2 ^ count * ((store.read
          (.storage (BasisLayout.secondRow ctx width).first.toCStorageRef)).toNat + 1)) %
          2 ^ width ∧
      ((storeStep first second width count store).read
        (.storage (BasisLayout.thirdRow ctx width).second.toCStorageRef)).toNat =
        (2 ^ count * ((store.read
          (.storage (BasisLayout.thirdRow ctx width).second.toCStorageRef)).toNat + 1)) %
          2 ^ width := by
  let firstResult := FirstRow.storeStep (BasisLayout.underRead first width)
    (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width) store
  let secondResult := PowerOfTwo.storeStep count (BasisLayout.secondRow ctx width).first firstResult
  have secondBefore := FirstRow.nativeLattice_firstRow_read_other
    (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width)
    (.storage (BasisLayout.secondRow ctx width).first.toCStorageRef)
    (key_free ctx width 11 8 (by decide)) (key_free ctx width 10 8 (by decide))
    (key_free ctx width 9 8 (by decide)) store
  have thirdBeforeFirst := FirstRow.nativeLattice_firstRow_read_other
    (BasisLayout.underRead first width) (BasisLayout.underRead second width)
    (BasisLayout.firstRow ctx width)
    (.storage (BasisLayout.thirdRow ctx width).second.toCStorageRef)
    (key_free ctx width 11 4 (by decide)) (key_free ctx width 10 4 (by decide))
    (key_free ctx width 9 4 (by decide)) store
  have thirdBeforeSecond := PowerOfTwo.nativeLattice_powerOfTwo_read_other count
    (BasisLayout.secondRow ctx width).first
    (.storage (BasisLayout.thirdRow ctx width).second.toCStorageRef)
    (key_free ctx width 8 4 (by decide)) firstResult
  have secondAfterThird := PowerOfTwo.nativeLattice_powerOfTwo_read_other count
    (BasisLayout.thirdRow ctx width).second
    (.storage (BasisLayout.secondRow ctx width).first.toCStorageRef)
    (key_free ctx width 4 8 (by decide)) secondResult
  have secondValue := PowerOfTwo.nativeLattice_powerOfTwo_read count
    (BasisLayout.secondRow ctx width).first firstResult
  have thirdValue := PowerOfTwo.nativeLattice_powerOfTwo_read count
    (BasisLayout.thirdRow ctx width).second secondResult
  exact ⟨(congrArg CShape.Value.toNat secondAfterThird).trans
    (secondValue.trans (congrArg (fun value : CShape.Value (.unsignedWord width) =>
      (2 ^ count * (value.toNat + 1)) % 2 ^ width) secondBefore)),
    thirdValue.trans (congrArg (fun value : CShape.Value (.unsignedWord width) =>
      (2 ^ count * (value.toNat + 1)) % 2 ^ width)
      (thirdBeforeSecond.trans thirdBeforeFirst))⟩

/-- Every actual structural read outside the five written coordinates survives initialization. -/
theorem nativeLattice_basis_initialization_read_other
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    {shape : CShape} (other : CInputRef (BasisLayout.context ctx width) shape)
    (firstFree : (BasisLayout.firstRow ctx width).first.key ∉ other.storageKeys)
    (secondFree : (BasisLayout.firstRow ctx width).second.key ∉ other.storageKeys)
    (thirdFree : (BasisLayout.firstRow ctx width).third.key ∉ other.storageKeys)
    (secondPowerFree : (BasisLayout.secondRow ctx width).first.key ∉ other.storageKeys)
    (thirdPowerFree : (BasisLayout.thirdRow ctx width).second.key ∉ other.storageKeys)
    (store : Store (BasisLayout.context ctx width)) :
    (storeStep first second width count store).read other = store.read other := by
  let firstResult := FirstRow.storeStep (BasisLayout.underRead first width)
    (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width) store
  let secondResult := PowerOfTwo.storeStep count (BasisLayout.secondRow ctx width).first firstResult
  exact (PowerOfTwo.nativeLattice_powerOfTwo_read_other count
    (BasisLayout.thirdRow ctx width).second other thirdPowerFree secondResult).trans
    ((PowerOfTwo.nativeLattice_powerOfTwo_read_other count
      (BasisLayout.secondRow ctx width).first other secondPowerFree firstResult).trans
      (FirstRow.nativeLattice_firstRow_read_other (BasisLayout.underRead first width)
        (BasisLayout.underRead second width) (BasisLayout.firstRow ctx width)
        other firstFree secondFree thirdFree store))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
