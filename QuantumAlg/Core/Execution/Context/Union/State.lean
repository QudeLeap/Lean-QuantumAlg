/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Context.Union.Basis
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws
import all QuantumAlg.Core.Execution.State.Coordinate.Transport
import all QuantumAlg.Core.Execution.State

/-!
# Complete state coordinates for a physically present runtime frame

Both contexts remain physically present in their actual union. For a
local-execution proof only, their exact wire and store correspondences
reassociate the untouched frame beside the external reference. Every
classical frame value remains a separate block label, and every quantum
frame coordinate remains in the full density matrix. No product-state
or independence assumption is made
[dW19, qcnotes.tex:389,5381,5394,6827].

These inverse coordinate changes emit no circuit and make no resource
claim. The actual enclosing circuit still owns the complete union, whose
resident space includes both original contexts.
-/

namespace QuantumAlg.Execution.ContextUnion

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} (left right : RuntimeCtx kind)
  (separate : RuntimeCtx.StorageDisjoint left right)

/-- Reassociate actual quantum wire coordinates beside the same external reference. -/
def referenceBasis (Reference : Register) :
    (Register.prod (left.disjointUnion right separate).register Reference).Index ≃
      (Register.prod left.register (Register.prod right.register Reference)).Index :=
  ((unionBasisEquiv left right separate).prodCongr (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc left.register.Index right.register.Index Reference.Index)

/-- Retain the complete right store alongside the original mathematical history. -/
def recordEquiv (History : Type) :
    (Store (left.disjointUnion right separate) × History) ≃
      (Store left × (Store right × History)) :=
  ((storeEquiv separate).prodCongr (Equiv.refl History)).trans
    (Equiv.prodAssoc (Store left) (Store right) History)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Exact proof coordinates retain all frame classical labels and all frame quantum systems. -/
def splitState (state : State (left.disjointUnion right separate) Reference History) :
    State left (Register.prod right.register Reference) (Store right × History) :=
  (state.mapClassical (recordEquiv left right separate History)).reindex
    (referenceBasis left right separate Reference)

/-- Put the persistent service before the retained frame store, without discarding either. -/
def serviceHistory (Hidden History : Type) :
    Store right × (Hidden × History) ≃ Hidden × (Store right × History) where
  toFun record := (record.2.1, (record.1, record.2.2))
  invFun record := (record.2.1, (record.1, record.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The same joint frame coordinates with a distinct persistent service label. -/
def splitServiceState {Hidden H : Type} [Fintype Hidden] [Fintype H]
    (state : State (left.disjointUnion right separate) Reference (Hidden × H)) :
    State left (Register.prod right.register Reference) (Hidden × (Store right × H)) :=
  (splitState left right separate state).mapHistory (serviceHistory right Hidden H)

/-- Reconstruct the actual union state without discarding any block or quantum coordinate. -/
def joinState
    (state : State left (Register.prod right.register Reference) (Store right × History)) :
    State (left.disjointUnion right separate) Reference History :=
  (state.mapClassical (recordEquiv left right separate History).symm).reindex
    (referenceBasis left right separate Reference).symm

/-- Splitting and reconstructing preserves the complete actual classical-quantum state. -/
theorem contextUnion_join_split_state
    (state : State (left.disjointUnion right separate) Reference History) :
    joinState left right separate (splitState left right separate state) = state :=
  ExecutionState.coordinate_transport_inverse state (recordEquiv left right separate History)
    (referenceBasis left right separate Reference)

/-- Reconstruction and splitting are inverse on arbitrary correlated frame states too. -/
theorem contextUnion_split_join_state
    (state : State left (Register.prod right.register Reference) (Store right × History)) :
    splitState left right separate (joinState left right separate state) = state :=
  ExecutionState.coordinate_transport_inverse state
    (recordEquiv left right separate History).symm
    (referenceBasis left right separate Reference).symm

/-- A split coordinate block is exactly the original full density block, entry for entry. -/
theorem contextUnion_splitState_entry
    (state : State (left.disjointUnion right separate) Reference History)
    (label : Store left × (Store right × History))
    (row column : (Register.prod left.register (Register.prod right.register Reference)).Index) :
    ((splitState left right separate state).block label).matrix row column =
      (state.block ((recordEquiv left right separate History).symm label)).matrix
        ((referenceBasis left right separate Reference).symm row)
        ((referenceBasis left right separate Reference).symm column) :=
  ExecutionState.coordinate_transport_entry state (recordEquiv left right separate History)
    (referenceBasis left right separate Reference) label row column

end

end QuantumAlg.Execution.ContextUnion
