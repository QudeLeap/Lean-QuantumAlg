/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Initialization.Readout

/-!
# Complete source basis from the actual fresh coordinate layout

The real twelve-word allocation and original loading sequence produce the
rows (j1, j2, 1), (2^count, 0, 0), and (0, 2^count, 0), with each entry reduced
only to its actual word capacity. All three target coordinates remain zero.
The j values come from the original structural source reads before entry.
There are no caller initialization or storage-separation assumptions.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth : Nat}

private theorem untouched_read
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (output : CWriteRef (BasisLayout.context ctx width) (.unsignedWord width))
    (index : Fin 12) (key : output.key = BasisLayout.cellKey ctx width index)
    (untouched : index ∉ ([11, 10, 9, 8, 4] : List (Fin 12)))
    (store : Store (BasisLayout.context ctx width)) :
    (storeStep first second width count store).read (.storage output.toCStorageRef) =
      store.read (.storage output.toCStorageRef) := by
  have different (written : Fin 12) (present : written ∈ ([11, 10, 9, 8, 4] : List (Fin 12))) :
      written ≠ index := fun same => untouched (same ▸ present)
  have free (written : Fin 12)
      (destination : CWriteRef (BasisLayout.context ctx width) (.unsignedWord width))
      (destinationKey : destination.key = BasisLayout.cellKey ctx width written)
      (present : written ∈ ([11, 10, 9, 8, 4] : List (Fin 12))) :
      destination.key ∉ (.storage output.toCStorageRef : CInputRef
        (BasisLayout.context ctx width) (.unsignedWord width)).storageKeys := by
    have unequal : destination.key ≠ output.key := by
      intro collision
      exact BasisLayout.nativeLattice_basis_key_ne ctx width written index
        (different written present) (destinationKey.symm.trans (collision.trans key))
    simpa only [CInputRef.storageKeys, List.mem_singleton] using unequal
  exact nativeLattice_basis_initialization_read_other first second width count
    (.storage output.toCStorageRef)
    (free 11 (BasisLayout.firstRow ctx width).first rfl (by decide))
    (free 10 (BasisLayout.firstRow ctx width).second rfl (by decide))
    (free 9 (BasisLayout.firstRow ctx width).third rfl (by decide))
    (free 8 (BasisLayout.secondRow ctx width).first rfl (by decide))
    (free 4 (BasisLayout.thirdRow ctx width).second rfl (by decide)) store

/-- Actual fresh entry and native loading produce all nine source basis and three target values. -/
theorem nativeLattice_basis_initialization_source
    (first second : CInputRef ctx (.unsignedWord sourceWidth)) (width count : Nat)
    (store : Store ctx) :
    let result := storeStep first second width count (BasisLayout.pushStore width store)
    BasisLayout.rowValues (BasisLayout.firstRow ctx width) result =
        ((store.read first).toNat % 2 ^ width, (store.read second).toNat % 2 ^ width,
          1 % 2 ^ width) ∧
      BasisLayout.rowValues (BasisLayout.secondRow ctx width) result =
        (2 ^ count % 2 ^ width, 0, 0) ∧
      BasisLayout.rowValues (BasisLayout.thirdRow ctx width) result =
        (0, 2 ^ count % 2 ^ width, 0) ∧
      BasisLayout.rowValues (BasisLayout.target ctx width) result = (0, 0, 0) := by
  let entered : Store (BasisLayout.context ctx width) := BasisLayout.pushStore width store
  have initial := BasisLayout.nativeLattice_basis_initial_zero width store
  have firstRow := nativeLattice_basis_initialization_first_row first second width count entered
  have powers := nativeLattice_basis_initialization_power_values first second width count entered
  have firstInput := congrArg (fun value : CShape.Value (.unsignedWord sourceWidth) =>
    value.toNat % 2 ^ width) (BasisLayout.nativeLattice_basis_push_read first width store)
  have secondInput := congrArg (fun value : CShape.Value (.unsignedWord sourceWidth) =>
    value.toNat % 2 ^ width) (BasisLayout.nativeLattice_basis_push_read second width store)
  have firstThird := congrArg (fun values : Nat × Nat × Nat =>
    (values.2.2 + 1) % 2 ^ width) initial.1
  have secondPower : ((storeStep first second width count entered).read
      (.storage (BasisLayout.secondRow ctx width).first.toCStorageRef)).toNat =
        2 ^ count % 2 ^ width := by
    simpa only [Nat.zero_add, Nat.mul_one] using powers.1.trans
      (congrArg (fun values : Nat × Nat × Nat =>
        (2 ^ count * (values.1 + 1)) % 2 ^ width) initial.2.1)
  have thirdPower : ((storeStep first second width count entered).read
      (.storage (BasisLayout.thirdRow ctx width).second.toCStorageRef)).toNat =
        2 ^ count % 2 ^ width := by
    simpa only [Nat.zero_add, Nat.mul_one] using powers.2.trans
      (congrArg (fun values : Nat × Nat × Nat =>
        (2 ^ count * (values.2.1 + 1)) % 2 ^ width) initial.2.2.1)
  have secondSecond := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.secondRow ctx width).second
      7 rfl (by decide) entered)
  have secondThird := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.secondRow ctx width).third
      6 rfl (by decide) entered)
  have thirdFirst := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.thirdRow ctx width).first
      5 rfl (by decide) entered)
  have thirdThird := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.thirdRow ctx width).third
      3 rfl (by decide) entered)
  have targetFirst := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.target ctx width).first
      2 rfl (by decide) entered)
  have targetSecond := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.target ctx width).second
      1 rfl (by decide) entered)
  have targetThird := congrArg CShape.Value.toNat
    (untouched_read first second width count (BasisLayout.target ctx width).third
      0 rfl (by decide) entered)
  refine ⟨firstRow.trans (Prod.ext firstInput (Prod.ext secondInput firstThird)), ?_, ?_, ?_⟩
  · exact Prod.ext secondPower (Prod.ext
      (secondSecond.trans (congrArg (fun values : Nat × Nat × Nat => values.2.1) initial.2.1))
      (secondThird.trans (congrArg (fun values : Nat × Nat × Nat => values.2.2) initial.2.1)))
  · exact Prod.ext
      (thirdFirst.trans (congrArg (fun values : Nat × Nat × Nat => values.1) initial.2.2.1))
      (Prod.ext thirdPower
        (thirdThird.trans (congrArg (fun values : Nat × Nat × Nat => values.2.2) initial.2.2.1)))
  · exact Prod.ext
      (targetFirst.trans (congrArg (fun values : Nat × Nat × Nat => values.1) initial.2.2.2))
      (Prod.ext
        (targetSecond.trans (congrArg (fun values : Nat × Nat × Nat => values.2.1) initial.2.2.2))
        (targetThird.trans (congrArg (fun values : Nat × Nat × Nat => values.2.2) initial.2.2.2)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisInitialization
