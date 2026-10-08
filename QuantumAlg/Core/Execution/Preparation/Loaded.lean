/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Coordinates
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Entries

/-!
# Place a native loader on newly allocated physical systems

The fresh positions are selected from the actual preparation context. A
native operation on these systems retains every old basis value, including
arbitrary dirty inputs. This is the exact physical bridge for a zero
allocation followed by actual gates that load a fixed seed.
-/

namespace QuantumAlg.Execution.PreparationLoaded

noncomputable section

variable {count : Nat} (ctx : RuntimeCtx .quantum) (key : StorageKey)
  (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
  (disjoint : List.Disjoint layout.identities ctx.physicalIdx)

/-- Newly allocated systems occupy precisely the preparation's fresh positions. -/
def position : Fin count ↪ Fin (ctx.addOwnedLayout key layout fresh disjoint).systemCount where
  toFun index := PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint (.inl index)
  inj' := by
    intro left right same
    exact Sum.inl.inj
      ((PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint).injective same)

private theorem dimensions (index : Fin count) :
    (layout.wire index).dimension =
      ((ctx.addOwnedLayout key layout fresh disjoint).quantumLayout.wire
        (position ctx key layout fresh disjoint index)).dimension := by
  exact congrArg QuantumWire.dimension
    (PreparationBorrowed.fullPositionEquiv_new_wire ctx key layout fresh disjoint index).symm

/-- Place every actual native gate on the fresh wires and leave old systems in the layout. -/
def program {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles layout) :
    UnitaryCircuit gates oracles
      (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout :=
  UnitaryCircuit.placeAt layout (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout
    (position ctx key layout fresh disjoint) (dimensions ctx key layout fresh disjoint) body

/-- A proved native basis action on the fresh bank preserves the complete old basis. -/
theorem program_joined_ket {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles layout) (input output : layout.Basis)
    (action : body.applyNormalized (NormalizedVector.ket input) = NormalizedVector.ket output)
    (old : ctx.register.Index) :
    (program ctx key layout fresh disjoint body).applyNormalized
        (NormalizedVector.ket
          (preparedLocalBasisEquiv ctx key layout fresh disjoint (input, old))) =
      NormalizedVector.ket
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (output, old)) := by
  unfold program
  apply UnitaryCircuit.placeAt_applyNormalized_ket_of_eq
    layout (ctx.addOwnedLayout key layout fresh disjoint).quantumLayout
    (position ctx key layout fresh disjoint) (dimensions ctx key layout fresh disjoint)
    body input output action
  · funext index
    apply Fin.ext
    change (preparedLocalBasisEquiv ctx key layout fresh disjoint (input, old)
      (position ctx key layout fresh disjoint index)).val = (input index).val
    exact preparedLocalBasisEquiv_new_value ctx key layout fresh disjoint input old index
  · funext index
    apply Fin.ext
    change (preparedLocalBasisEquiv ctx key layout fresh disjoint (output, old)
      (position ctx key layout fresh disjoint index)).val = (output index).val
    exact preparedLocalBasisEquiv_new_value ctx key layout fresh disjoint output old index
  · funext index
    obtain ⟨original, same⟩ :=
      (PreparationBorrowed.fullPositionEquiv ctx key layout fresh disjoint).surjective index.val
    cases original with
    | inl freshIndex =>
      have member : index.val ∈ Finset.univ.map (position ctx key layout fresh disjoint) := by
        rw [← same]
        exact Finset.mem_map_of_mem _ (Finset.mem_univ freshIndex)
      exact False.elim ((Finset.mem_compl.mp index.property) member)
    | inr oldIndex =>
      apply Fin.ext
      have first := preparedLocalBasisEquiv_old_value ctx key layout fresh disjoint
        output old oldIndex
      have second := preparedLocalBasisEquiv_old_value ctx key layout fresh disjoint
        input old oldIndex
      change (preparedLocalBasisEquiv ctx key layout fresh disjoint (output, old)
        index.val).val =
          (preparedLocalBasisEquiv ctx key layout fresh disjoint (input, old)
            index.val).val
      rw [← same]
      exact first.trans second.symm

theorem program_eventTrace {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles layout) :
    (program ctx key layout fresh disjoint body).eventTrace = body.eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

theorem program_eventCost {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles layout) :
    (program ctx key layout fresh disjoint body).eventCost = body.eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

theorem program_unitDepth {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles layout) :
    (program ctx key layout fresh disjoint body).evaluatedEventDepth (fun _ => 1) =
      body.evaluatedEventDepth (fun _ => 1) :=
  UnitaryCircuit.placeAt_evaluatedEventDepth _ _ _ _ _ _

end

end QuantumAlg.Execution.PreparationLoaded
