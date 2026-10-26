/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.RetainedTables
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Preparation.Signed.Specification
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Measurement.Cells.Borrowed

/-! # Original borrowed inputs through the actual bank and table allocations -/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Factory

open QuantumAlg.Execution QuantumAlg.ClassicalRoutines.EllipticCurve
noncomputable section
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- Project only the newly allocated table, result and owned-bank Store entries. -/
def originalStoreAfterTables (store : Store (tableContext base noQuantum)) : Store base :=
  let results := RetainedCells.originalStore (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256) store
  let bank := MeasurementCells.originalStore 2 520 results
  ⟨bank.cells.2⟩

private lemma ownedTail_read {ctx : RuntimeCtx .quantum}
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (store : Store (ctx.addOwnedLayout key layout fresh disjoint))
    {shape : CShape} (input : CInputRef ctx shape) :
    (Store.mk store.cells.2).read input =
      store.read (input.underOwnedLayout key layout fresh disjoint) := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH => exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source ih => exact congrArg CShape.Value.first ih
  | second source ih => exact congrArg CShape.Value.second ih
  | vectorGet source index ih => exact congrArg (fun value => value.get index) ih
  | bitsGet source index ih => exact congrArg (fun value => value.bitGet index) ih
  | wordBitGet source index ih => exact congrArg (fun value => value.wordBitGet index) ih

private lemma ownedTail_borrowed {ctx : RuntimeCtx .quantum}
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (store : Store (ctx.addOwnedLayout key layout fresh disjoint)) :
    HEq store.readBorrowedClassical (Store.mk store.cells.2).readBorrowedClassical := by
  rfl

attribute [local irreducible] RetainedCells.originalStore MeasurementCells.originalStore

/-- Every transported original input reads the projected original Store. -/
lemma originalStoreAfterTables_read (store : Store (tableContext base noQuantum))
    {shape : CShape} (input : CInputRef base shape) :
    (originalStoreAfterTables base noQuantum store).read input =
      store.read (originalInputAfterTables base noQuantum input) := by
  let retained := RetainedCells.originalStore (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256) store
  let bank := MeasurementCells.originalStore (ctx := bankContext base noQuantum) 2 520 retained
  have first := ownedTail_read base.canonicalFreshKey
    (QubitLayout.canonical
      PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.encoding.width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum) bank input
  have second := MeasurementCells.originalStore_read (ctx := bankContext base noQuantum)
    2 520 retained (input.underOwnedLayout base.canonicalFreshKey
      (QubitLayout.canonical
        PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.encoding.width).toQuantum
      base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum))
  have third := RetainedCells.originalStore_read (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256) store (originalInput base noQuantum input)
  exact first.trans (second.trans third)

/-- The same projection retains the complete borrowed observation, including both public points. -/
lemma originalStoreAfterTables_borrowed (store : Store (tableContext base noQuantum)) :
    HEq store.readBorrowedClassical
      (originalStoreAfterTables base noQuantum store).readBorrowedClassical := by
  let retained := RetainedCells.originalStore (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256) store
  let bank := MeasurementCells.originalStore (ctx := bankContext base noQuantum) 2 520 retained
  have first := RetainedCells.originalStore_borrowed (resultContext base noQuantum)
    (WindowTables.Outer.sharedShapes 256) store
  have second := MeasurementCells.originalStore_borrowed
    (ctx := bankContext base noQuantum) 2 520 retained
  exact first.trans (second.trans (ownedTail_borrowed base.canonicalFreshKey
    (QubitLayout.canonical
      PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.encoding.width).toQuantum
    base.runtimeCtx_canonicalFreshKey_fresh (bankDisjoint base noQuantum) bank))

/-- Fresh allocation discharges separation from every original structural input. -/
lemma tableFrame_original_inputFree {shape : CShape} (input : CInputRef base shape) :
    WindowTables.Outer.Preparation.Signed.InputFree (tableFrame base noQuantum)
      (originalInputAfterTables base noQuantum input) :=
  WindowTables.Outer.Frame.retained_key_avoids_original (resultContext base noQuantum)
    256 (originalInput base noQuantum input)

/-- Every supported allocation output inherits an actual supported original borrowed observation. -/
lemma prepareWithTables_supported_original {services : ClassicalOracleModel}
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (value : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
        BitWord.model services).HiddenState ×
        (History × (prepareWithTables (services := services) base noQuantum).Path)))
    (positive : 0 < (((prepareWithTables (services := services) base noQuantum).execute
      environment Reference state).block value).mass) :
    ∃ original, 0 < (state.block original).mass ∧
      original.1.readBorrowedClassical =
        (originalStoreAfterTables base noQuantum value.1).readBorrowedClassical := by
  let code := prepareWithTables (services := services) base noQuantum
  have noBorrowed : base.borrowedQuantumWires = [] := by
    have sub := base.borrowedQuantumWires_sublist
    rw [noQuantum] at sub
    exact List.sublist_nil.mp sub
  have restored := code.borrowedRestored_of_noBorrowedQuantum environment
    noBorrowed Reference state
  obtain ⟨original, supported, same⟩ := code.borrowedRestored_supported_initial Reference
    state (code.execute environment Reference state) restored value positive
  refine ⟨original, supported, eq_of_heq ?_⟩
  have castSame : HEq (code.borrowedClassicalValueTransport value.1.readBorrowedClassical)
      value.1.readBorrowedClassical :=
    ((Equiv.cast_eq_iff_heq
      (congrArg CShape.Value code.borrowedClassicalShape_preserved)).mp rfl).symm
  exact (heq_of_eq same).trans
    (castSame.trans (originalStoreAfterTables_borrowed base noQuantum value.1))

attribute [local irreducible] Store.read originalInputAfterTables originalStoreAfterTables
  Circuit.execute prepareWithTables

/-- Actual allocation preserves any predicate on two original borrowed input values. -/
lemma prepareWithTables_read_pair_on_support {services : ClassicalOracleModel}
    {firstShape secondShape : CShape}
    (first : CInputRef base firstShape) (second : CInputRef base secondShape)
    (readsBorrowed : ∀ initial final : Store base,
      initial.readBorrowedClassical = final.readBorrowedClassical →
        initial.read first = final.read first ∧ initial.read second = final.read second)
    (property : CShape.Value firstShape → CShape.Value secondShape → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
      BitWord.model services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference ((ExecutionModel.quantum AlgorithmGate.model
      OracleModel.empty BitWord.model services).HiddenState × History))
    (supported : ∀ initial, 0 < (state.block initial).mass →
      property (initial.1.read first) (initial.1.read second))
    (value : Store (tableContext base noQuantum) ×
      ((ExecutionModel.quantum AlgorithmGate.model OracleModel.empty
        BitWord.model services).HiddenState ×
        (History × (prepareWithTables (services := services) base noQuantum).Path)))
    (positive : 0 < (((prepareWithTables (services := services) base noQuantum).execute
      environment Reference state).block value).mass) :
    property (value.1.read (originalInputAfterTables base noQuantum first))
      (value.1.read (originalInputAfterTables base noQuantum second)) := by
  obtain ⟨original, originalPositive, sameBorrowed⟩ :=
    prepareWithTables_supported_original base noQuantum environment Reference state value positive
  have reads := readsBorrowed original.1
    (originalStoreAfterTables base noQuantum value.1) sameBorrowed
  have firstRead := reads.1.trans
    (originalStoreAfterTables_read base noQuantum value.1 first)
  have secondRead := reads.2.trans
    (originalStoreAfterTables_read base noQuantum value.1 second)
  exact (congrArg₂ property firstRead secondRead).mp (supported original originalPositive)

end
end QuantumAlg.EllipticCurve.P256.Measured.Window.Factory
