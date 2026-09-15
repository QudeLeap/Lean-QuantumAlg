/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Basis.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Row.Store

/-!
# Actual initialization of all basis and target coordinates

The twelve individual words are initialized by their real nested lexical
scopes. Their values are observed directly through the intrinsic writable
references. The proofs compose the three-cell row laws at named stores,
retaining all original structural input values without expanding the entire
work layout into an alternative state representation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Observe the three actual word values of one row without allocating or packing storage. -/
def rowValues {ctx : RuntimeCtx kind} {width : Nat}
    (row : FirstRow.Refs ctx width) (store : Store ctx) : Nat × Nat × Nat :=
  ((store.read (.storage row.first.toCStorageRef)).toNat,
    (store.read (.storage row.second.toCStorageRef)).toNat,
    (store.read (.storage row.third.toCStorageRef)).toNat)

private theorem rowValues_push_lift {width : Nat}
    (row : FirstRow.Refs ctx width) (store : Store ctx) :
    rowValues (liftRow row) (RowLayout.pushStore width store) = rowValues row store := by
  have first := RowLayout.nativeLattice_row_push_read
    (.storage row.first.toCStorageRef) width store
  have second := RowLayout.nativeLattice_row_push_read
    (.storage row.second.toCStorageRef) width store
  have third := RowLayout.nativeLattice_row_push_read
    (.storage row.third.toCStorageRef) width store
  exact Prod.ext (congrArg CShape.Value.toNat first)
    (Prod.ext (congrArg CShape.Value.toNat second) (congrArg CShape.Value.toNat third))

private theorem rowValues_zero (width : Nat) (store : Store ctx) :
    rowValues (RowLayout.refs ctx width) (RowLayout.pushStore width store) = (0, 0, 0) := by
  have actual := RowLayout.nativeLattice_row_initial_zero width store
  exact Prod.ext actual.1 (Prod.ext actual.2.1 actual.2.2)

/-- Actual entry supplies all nine basis and all three target zero words without input premises. -/
theorem nativeLattice_basis_initial_zero (width : Nat) (store : Store ctx) :
    rowValues (firstRow ctx width) (pushStore width store) = (0, 0, 0) ∧
      rowValues (secondRow ctx width) (pushStore width store) = (0, 0, 0) ∧
      rowValues (thirdRow ctx width) (pushStore width store) = (0, 0, 0) ∧
      rowValues (target ctx width) (pushStore width store) = (0, 0, 0) := by
  let first : Store (context1 ctx width) := RowLayout.pushStore width store
  let second : Store (context2 ctx width) := RowLayout.pushStore width first
  let third : Store (context3 ctx width) := RowLayout.pushStore width second
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rowValues_push_lift
      (liftRow (liftRow (RowLayout.refs ctx width))) third).trans
      ((rowValues_push_lift (liftRow (RowLayout.refs ctx width)) second).trans
        ((rowValues_push_lift (RowLayout.refs ctx width) first).trans (rowValues_zero width store)))
  · exact (rowValues_push_lift
      (liftRow (RowLayout.refs (context1 ctx width) width)) third).trans
      ((rowValues_push_lift (RowLayout.refs (context1 ctx width) width) second).trans
        (rowValues_zero width first))
  · exact (rowValues_push_lift (RowLayout.refs (context2 ctx width) width) third).trans
      (rowValues_zero width second)
  · exact rowValues_zero width third

/-- Actual entry preserves every original structural source beneath all four row scopes. -/
theorem nativeLattice_basis_push_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store ctx) :
    (pushStore width store).read (underRead input width) = store.read input := by
  let firstRef : CInputRef (context1 ctx width) shape := RowLayout.underRead input width
  let secondRef : CInputRef (context2 ctx width) shape := RowLayout.underRead firstRef width
  let thirdRef : CInputRef (context3 ctx width) shape := RowLayout.underRead secondRef width
  let first : Store (context1 ctx width) := RowLayout.pushStore width store
  let second : Store (context2 ctx width) := RowLayout.pushStore width first
  let third : Store (context3 ctx width) := RowLayout.pushStore width second
  exact (RowLayout.nativeLattice_row_push_read thirdRef width third).trans
    ((RowLayout.nativeLattice_row_push_read secondRef width second).trans
      ((RowLayout.nativeLattice_row_push_read firstRef width first).trans
        (RowLayout.nativeLattice_row_push_read input width store)))

/-- Actual reverse release exposes the corresponding original read beneath all twelve words. -/
theorem nativeLattice_basis_pop_read {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) (store : Store (context ctx width)) :
    (popStore width store).read input = store.read (underRead input width) := by
  let firstRef : CInputRef (context1 ctx width) shape := RowLayout.underRead input width
  let secondRef : CInputRef (context2 ctx width) shape := RowLayout.underRead firstRef width
  let thirdRef : CInputRef (context3 ctx width) shape := RowLayout.underRead secondRef width
  let third : Store (context3 ctx width) := RowLayout.popStore width store
  let second : Store (context2 ctx width) := RowLayout.popStore width third
  let first : Store (context1 ctx width) := RowLayout.popStore width second
  exact (RowLayout.nativeLattice_row_pop_read input width first).trans
    ((RowLayout.nativeLattice_row_pop_read firstRef width second).trans
      ((RowLayout.nativeLattice_row_pop_read secondRef width third).trans
        (RowLayout.nativeLattice_row_pop_read thirdRef width store)))

/-- Structural lifting retains the exact original storage-key support below the four rows. -/
theorem nativeLattice_basis_underRead_keys {shape : CShape}
    (input : CInputRef ctx shape) (width : Nat) :
    (underRead input width).storageKeys = input.storageKeys := by
  let first : CInputRef (context1 ctx width) shape := RowLayout.underRead input width
  let second : CInputRef (context2 ctx width) shape := RowLayout.underRead first width
  let third : CInputRef (context3 ctx width) shape := RowLayout.underRead second width
  exact (RowLayout.nativeLattice_row_underRead_keys third width).trans
    ((RowLayout.nativeLattice_row_underRead_keys second width).trans
      ((RowLayout.nativeLattice_row_underRead_keys first width).trans
        (RowLayout.nativeLattice_row_underRead_keys input width)))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.BasisLayout
