/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Preparation.Basis
import all QuantumAlg.Core.Execution.Context.Union.Unitary.State
import all QuantumAlg.Core.Execution.Context.Union.State.Laws
import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.Prepared.BasisSupport

/-!
# Complete state naturality of actual framed preparation

The existing preparation adds its actual physical basis and its actual
classical presence marker. Splitting beside a resident frame commutes with
this instruction on every classical block and every complete quantum and
reference matrix entry. No independence or initial-value condition is imposed
on any previously present system.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def preparedStoreEquiv {ctx : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    Store ctx ≃ Store (ctx.addOwnedLayout key layout fresh disjoint) where
  toFun store := store.pushOwnedLayout key layout fresh disjoint
  invFun store := ⟨store.cells.2⟩
  left_inv _ := rfl
  right_inv store := by
    rcases store with ⟨marker, cells⟩
    cases marker
    rfl

private def preparationRecordEquiv {ctx : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) (History : Type) :
    (Store ctx × History) ≃
      (Store (ctx.addOwnedLayout key layout fresh disjoint) × (History × Unit)) where
  toFun record := (record.1.pushOwnedLayout key layout fresh disjoint, (record.2, ()))
  invFun record := ((preparedStoreEquiv key layout fresh disjoint).symm record.1, record.2.1)
  left_inv _ := rfl
  right_inv record := by
    rcases record with ⟨store, history, path⟩
    cases path
    exact Prod.ext ((preparedStoreEquiv key layout fresh disjoint).apply_symm_apply store) rfl

private theorem prepared_block {ctx : RuntimeCtx .quantum} {count : Nat}
    (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (store : Store ctx) (history : History) :
    (state.prepare key layout fresh disjoint preparation).block
      (store.pushOwnedLayout key layout fresh disjoint, (history, ())) =
        preparedDensity key layout fresh disjoint preparation.normalized Reference
          (state.block (store, history)) := by
  apply DensityOperator.ext
  let labels := preparationRecordEquiv key layout fresh disjoint History
  change (∑ record, if labels record = labels (store, history) then
      ((prepareContext state key layout fresh disjoint preparation.normalized).block
        record).matrix else 0) =
    ((prepareContext state key layout fresh disjoint preparation.normalized).block
      (store, history)).matrix
  simp only [labels.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {ctx frame : RuntimeCtx .quantum} {count : Nat}
  (key : StorageKey) (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
  (separate : RuntimeCtx.StorageDisjoint (ctx.addOwnedLayout key layout fresh disjoint) frame)

private theorem prepared_store_join (store : Store ctx) (framed : Store frame) :
    join separate (store.pushOwnedLayout key layout fresh disjoint) framed =
      Store.pushOwnedLayout
        (join (preparation_original_disjoint key layout fresh disjoint separate) store framed)
        key layout (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate) := rfl

private theorem prepared_reference_join (Reference : Register)
    (newBasis : layout.register.Index) (oldBasis : ctx.register.Index)
    (frameBasis : frame.register.Index) (reference : Reference.Index) :
    (referenceBasis (ctx.addOwnedLayout key layout fresh disjoint) frame separate Reference).symm
      (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis),
        (frameBasis, reference)) =
      prepareContextBasisEquiv
        (ctx.disjointUnion frame (preparation_original_disjoint key layout fresh disjoint separate))
        Reference key layout (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate)
        (newBasis, (referenceBasis ctx frame
          (preparation_original_disjoint key layout fresh disjoint separate) Reference).symm
            (oldBasis, (frameBasis, reference))) := by
  change ((unionBasisEquiv (ctx.addOwnedLayout key layout fresh disjoint) frame separate).symm
      (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis), frameBasis),
        reference) =
    (preparedFramedBasisEquiv key layout fresh disjoint separate
      (newBasis, (unionBasisEquiv ctx frame
        (preparation_original_disjoint key layout fresh disjoint separate)).symm
          (oldBasis, frameBasis)), reference)
  exact congrArg (fun basis => (basis, reference))
    (preparedFramedBasis_join key layout fresh disjoint separate newBasis oldBasis frameBasis).symm

/-- Fresh preparation commutes with exact frame and reference reindexing. -/
theorem prepared_density_naturality {Reference : Register}
    (preparation : BasisPreparation layout)
    (density : DensityOperator (Register.prod
      (ctx.disjointUnion frame
        (preparation_original_disjoint key layout fresh disjoint separate)).register Reference)) :
    (preparedDensity key layout (preparation_fresh_union key layout fresh disjoint separate)
      (preparation_wires_union key layout fresh disjoint separate) preparation.normalized
      Reference density).reindex
        (referenceBasis (ctx.addOwnedLayout key layout fresh disjoint) frame separate Reference) =
      preparedDensity key layout fresh disjoint preparation.normalized
        (Register.prod frame.register Reference)
        (density.reindex (referenceBasis ctx frame
          (preparation_original_disjoint key layout fresh disjoint separate) Reference)) := by
  apply DensityOperator.ext
  funext row column
  rcases row with ⟨row, frameRow, referenceRow⟩
  rcases column with ⟨column, frameColumn, referenceColumn⟩
  obtain ⟨⟨newRow, oldRow⟩, rfl⟩ :=
    (preparedLocalBasisEquiv ctx key layout fresh disjoint).surjective row
  obtain ⟨⟨newColumn, oldColumn⟩, rfl⟩ :=
    (preparedLocalBasisEquiv ctx key layout fresh disjoint).surjective column
  let oldBasis := referenceBasis ctx frame
    (preparation_original_disjoint key layout fresh disjoint separate) Reference
  let finalBasis := referenceBasis (ctx.addOwnedLayout key layout fresh disjoint)
    frame separate Reference
  let actualFresh := preparation_fresh_union key layout fresh disjoint separate
  let actualDisjoint := preparation_wires_union key layout fresh disjoint separate
  let actual := preparedDensity key layout actualFresh actualDisjoint
    preparation.normalized Reference density
  let sourceRow := oldBasis.symm (oldRow, (frameRow, referenceRow))
  let sourceColumn := oldBasis.symm (oldColumn, (frameColumn, referenceColumn))
  change actual.matrix
      (finalBasis.symm (preparedLocalBasisEquiv ctx key layout fresh disjoint (newRow, oldRow),
        (frameRow, referenceRow)))
      (finalBasis.symm
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (newColumn, oldColumn),
          (frameColumn, referenceColumn))) = _
  calc
    _ = actual.matrix
        (prepareContextBasisEquiv _ Reference key layout actualFresh actualDisjoint
          (newRow, sourceRow))
        (prepareContextBasisEquiv _ Reference key layout actualFresh actualDisjoint
          (newColumn, sourceColumn)) :=
      congrArg₂ actual.matrix
        (prepared_reference_join key layout fresh disjoint separate Reference
          newRow oldRow frameRow referenceRow)
        (prepared_reference_join key layout fresh disjoint separate Reference
          newColumn oldColumn frameColumn referenceColumn)
    _ = (preparation.normalized.vec newRow * star (preparation.normalized.vec newColumn)) *
        density.matrix sourceRow sourceColumn :=
      preparedDensity_joined_entry key layout actualFresh actualDisjoint preparation.normalized
        density newRow newColumn sourceRow sourceColumn
    _ = _ :=
      (preparedDensity_joined_entry key layout fresh disjoint preparation.normalized
        (density.reindex oldBasis) newRow newColumn
        (oldRow, (frameRow, referenceRow)) (oldColumn, (frameColumn, referenceColumn))).symm

/-- A mathematical fixed-basis preparation commutes with splitting a resident frame. -/
private theorem prepared_splitState (preparation : BasisPreparation layout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate)) Reference History) :
    splitState (ctx.addOwnedLayout key layout fresh disjoint) frame separate
      (state.prepare key layout
        (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate) preparation) =
      ((splitState ctx frame
        (preparation_original_disjoint key layout fresh disjoint separate) state).prepare
          key layout fresh disjoint preparation).mapHistory
            (fun record => (record.1.1, (record.1.2, record.2))) := by
  let originalSeparate := preparation_original_disjoint key layout fresh disjoint separate
  let actualFresh := preparation_fresh_union key layout fresh disjoint separate
  let actualDisjoint := preparation_wires_union key layout fresh disjoint separate
  let post := ctx.addOwnedLayout key layout fresh disjoint
  let originalBasis := referenceBasis ctx frame originalSeparate Reference
  let finalBasis := referenceBasis post frame separate Reference
  let localState := splitState ctx frame originalSeparate state
  change splitState post frame separate
      (state.prepare key layout actualFresh actualDisjoint preparation) =
    (localState.prepare key layout fresh disjoint preparation).mapHistory _
  apply ExecutionState.ext
  rintro ⟨finalStore, frameStore, history, path⟩
  cases path
  obtain ⟨store, rfl⟩ := (preparedStoreEquiv key layout fresh disjoint).surjective finalStore
  let newStore := store.pushOwnedLayout key layout fresh disjoint
  let oldDensity := state.block (join originalSeparate store frameStore, history)
  calc
    (splitState post frame separate
        (state.prepare key layout actualFresh actualDisjoint preparation)).block
          (newStore, (frameStore, (history, ()))) =
      ((state.prepare key layout actualFresh actualDisjoint preparation).block
        (join separate newStore frameStore, (history, ()))).reindex finalBasis :=
      split_block post frame separate _ newStore frameStore (history, ())
    _ = (preparedDensity key layout actualFresh actualDisjoint preparation.normalized
        Reference oldDensity).reindex finalBasis := by
      rw [prepared_store_join, prepared_block]
    _ = preparedDensity key layout fresh disjoint preparation.normalized
        (Register.prod frame.register Reference) (oldDensity.reindex originalBasis) :=
      prepared_density_naturality key layout fresh disjoint separate preparation oldDensity
    _ = preparedDensity key layout fresh disjoint preparation.normalized
        (Register.prod frame.register Reference)
        (localState.block (store, (frameStore, history))) :=
      congrArg (preparedDensity key layout fresh disjoint preparation.normalized
        (Register.prod frame.register Reference))
        (split_block ctx frame originalSeparate state store frameStore history).symm
    _ = (localState.prepare key layout fresh disjoint preparation).block
        (newStore, ((frameStore, history), ())) :=
      (prepared_block key layout fresh disjoint preparation localState store
        (frameStore, history)).symm
    _ = ((localState.prepare key layout fresh disjoint preparation).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2)))).block
          (newStore, (frameStore, (history, ()))) :=
      by
        let histories : (Store frame × History) × Unit ≃
            Store frame × (History × Unit) := Equiv.prodAssoc _ _ _
        let prepared := localState.prepare key layout fresh disjoint preparation
        have labels :
            (fun record : Store post × ((Store frame × History) × Unit) =>
              (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) =
                ((Equiv.refl (Store post)).prodCongr histories) := by
          funext record
          rfl
        have mapped :
            prepared.mapHistory
                (fun record => (record.1.1, (record.1.2, record.2))) =
              prepared.mapClassical ((Equiv.refl (Store post)).prodCongr histories) := by
          dsimp only [State.mapHistory]
          exact ExecutionState.executionState_mapClassical_congr prepared labels
        change prepared.block (newStore, ((frameStore, history), ())) = _
        rw [mapped]
        rw [ExecutionState.coordinate_mapClassical_block]
        rfl

/-- The real zero-allocation instruction preserves the complete resident frame and service. -/
theorem prepareZeroFramed_execute {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate))
        Reference (services.HiddenState × History)) :
    splitServiceState (ctx.addOwnedLayout key layout fresh disjoint) frame separate
      ((Circuit.prepareZero (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) _ key layout
        (preparation_fresh_union key layout fresh disjoint separate)
        (preparation_wires_union key layout fresh disjoint separate)).execute
          Reference state) =
      ((Circuit.prepareZero (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) ctx key layout
        fresh disjoint).execute (Register.prod frame.register Reference)
          (splitServiceState ctx frame
            (preparation_original_disjoint key layout fresh disjoint separate) state)).mapHistory
              (fun record =>
                (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  rw [Circuit.execute_prepareZero, Circuit.execute_prepareZero]
  dsimp only [splitServiceState]
  erw [contextUnion_splitState_mapHistory]
  erw [prepared_splitState]
  let source := splitState ctx frame
    (preparation_original_disjoint key layout fresh disjoint separate) state
  let service := serviceHistory frame services.HiddenState History
  have commuted := State.mapHistory_prepare source service
    key layout fresh disjoint (BasisPreparation.zero layout)
  conv_rhs => erw [commuted]
  simp only [State.mapHistory_comp, Function.comp_def]
  rfl

/-- Actual zero allocation and fixed-bit loading retain the complete frame and service. -/
theorem prepareFramed_execute {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    (load : UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ctx.disjointUnion frame
      (preparation_original_disjoint key layout fresh disjoint separate))
        Reference (services.HiddenState × History)) :
    splitServiceState (ctx.addOwnedLayout key layout fresh disjoint) frame separate
      ((prepareFramed key layout fresh disjoint separate load).execute Reference state) =
      (((Circuit.prepareZero (gates := gates) (oracles := oracles)
        (operations := operations) (classicalOracles := services) ctx key layout
        fresh disjoint).seq
          (Circuit.unitary (operations := operations) (classicalOracles := services)
            load)).execute (Register.prod frame.register Reference)
              (splitServiceState ctx frame
                (preparation_original_disjoint key layout fresh disjoint separate)
                state)).mapHistory
                  (fun record =>
                    (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) := by
  let first := prepareZeroFramed key layout fresh disjoint separate
    (gates := gates) (oracles := oracles)
    (operations := operations) (services := services)
  let second := Circuit.unitary (operations := operations)
    (classicalOracles := services)
    (frameUnitary (ctx.addOwnedLayout key layout fresh disjoint) frame separate load)
  let localFirst := Circuit.prepareZero (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := services) ctx key layout fresh disjoint
  let localSecond := Circuit.unitary (operations := operations)
    (classicalOracles := services) load
  let middle := first.execute Reference state
  let final := second.execute Reference middle
  let initial := splitServiceState ctx frame
    (preparation_original_disjoint key layout fresh disjoint separate) state
  let update : ((History × Unit) × Unit) → History × (Unit × Unit) :=
    fun record => (record.1.1, (record.1.2, record.2))
  let moveFrame : ((Store frame × History) × Unit) → Store frame × (History × Unit) :=
    fun record => (record.1.1, (record.1.2, record.2))
  have firstNatural : splitServiceState (ctx.addOwnedLayout key layout fresh disjoint)
      frame separate middle =
        (localFirst.execute (Register.prod frame.register Reference) initial).mapHistory
          (fun record => (record.1, moveFrame record.2)) :=
    prepareZeroFramed_execute key layout fresh disjoint separate state
  have secondNatural : splitServiceState (ctx.addOwnedLayout key layout fresh disjoint)
      frame separate final =
        (localSecond.execute (Register.prod frame.register Reference)
          (splitServiceState (ctx.addOwnedLayout key layout fresh disjoint)
            frame separate middle)).mapHistory
              (fun record => (record.1,
                (record.2.1.1, (record.2.1.2, record.2.2)))) :=
    contextUnion_splitServiceState_unitary
      (ctx.addOwnedLayout key layout fresh disjoint) frame separate load middle
  have mapped := Circuit.execute_mapHistory localSecond
    (Register.prod frame.register Reference)
    (localFirst.execute (Register.prod frame.register Reference) initial) moveFrame
  have reassociated := contextUnion_splitServiceState_mapHistory
    (ctx.addOwnedLayout key layout fresh disjoint) frame separate final update
  change splitServiceState (ctx.addOwnedLayout key layout fresh disjoint) frame separate
    ((first.seq second).execute Reference state) = _
  rw [Circuit.execute_seq]
  change splitServiceState (ctx.addOwnedLayout key layout fresh disjoint) frame separate
      (final.mapHistory (fun record => (record.1, update record.2))) =
    ((localFirst.seq localSecond).execute (Register.prod frame.register Reference)
      initial).mapHistory
        (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))
  rw [reassociated, secondNatural, firstNatural]
  erw [mapped]
  conv_rhs => rw [Circuit.execute_seq]
  conv_lhs => erw [State.mapHistory_comp]
  conv_lhs => erw [State.mapHistory_comp]
  conv_rhs => erw [State.mapHistory_comp]
  rfl

end

end QuantumAlg.Execution.ContextUnion
