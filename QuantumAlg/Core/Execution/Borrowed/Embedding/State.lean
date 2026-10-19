/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Borrowed.Embedding.Density
public import QuantumAlg.Core.Execution.Borrowed.Embedding.Tagged
public import QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Classical
import all QuantumAlg.Core.Execution.Borrowed.Embedding.Density
import all QuantumAlg.Core.Execution.Borrowed.Embedding.Tagged
import all QuantumAlg.Core.Execution.Context.Embedding.Borrowed.Classical
import all QuantumAlg.Core.Execution.Context.Embedding
import all QuantumAlg.Core.Execution.Borrowed.State
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Exact joint borrowed observation of an embedded execution

The complete caller observation is recovered from the local borrowed
classical-quantum observation retaining the entire quantum frame, the entire
classical frame store tag and the original external reference. Only frame
systems that are not borrowed and irrelevant history are discarded. This is
an equality of the whole CQ state, including correlations between the two
borrowed interfaces [dW19, qcnotes.tex:389,5381].
-/

namespace QuantumAlg

noncomputable section

attribute [local instance] Classical.decEq

private def borrowedQuantum {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (Reference : Register) {C : Type} [Fintype C]
    (state : ExecutionState C (ctx.register.prod Reference)) :
    ExecutionState C (ctx.borrowedQuantumLayout.register.prod Reference) where
  block value := ctx.observeBorrowedWithReference Reference (state.block value)
  total_le_one := by
    simp only [RuntimeCtx.observeBorrowedWithReference_mass]
    exact state.total_le_one

private lemma borrowedQuantum_mapClassical {kind : ProblemKind} (ctx : RuntimeCtx kind)
    (Reference : Register) {C D : Type} [Fintype C] [Fintype D]
    (state : ExecutionState C (ctx.register.prod Reference)) (read : C → D) :
    borrowedQuantum ctx Reference (state.mapClassical read) =
      (borrowedQuantum ctx Reference state).mapClassical read := by
  apply ExecutionState.ext
  intro value
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨row, refRow⟩
  rcases column with ⟨column, refColumn⟩
  change (ctx.observeBorrowedWithReference Reference
    ((state.mapClassical read).block value)).matrix (row, refRow) (column, refColumn) = _
  rw [RuntimeCtx.observeBorrowedWithReference_entry]
  simp only [ExecutionState.mapClassical_block_matrix, Matrix.sum_apply,
    Matrix.ite_apply, Matrix.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  by_cases same : read original = value
  · simp only [same, if_true]
    exact (ctx.observeBorrowedWithReference_entry Reference (state.block original)
      row column refRow refColumn).symm
  · simp only [same, if_false, Finset.sum_const_zero]

namespace ContextEmbedding

open Execution

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Orthogonal mathematical labels for the complete unchanged frame store; no runtime allocation. -/
public def frameStoreTag : Register where
  Index := Store placement.frame
  fintype := inferInstance
  decEq := Classical.decEq _

private def reassembleBorrowedQuantum (Reference : Register) {C : Type} [Fintype C]
    (state : ExecutionState C
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference))) :
    ExecutionState C (caller.borrowedQuantumLayout.register.prod Reference) where
  block value := placement.reassembleBorrowedDensity Reference (state.block value)
  total_le_one := by
    simp only [placement.contextEmbedding_reassembleBorrowedDensity_mass]
    exact state.total_le_one

/-- Reconstruct the caller's complete borrowed CQ observation from the local observation and tag. -/
def reassembleBorrowed (Reference : Register)
    (state : ExecutionState (localCtx.borrowedClassicalShape.Value × Store placement.frame)
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference))) :
    ExecutionState caller.borrowedClassicalShape.Value
      (caller.borrowedQuantumLayout.register.prod Reference) :=
  placement.reassembleBorrowedQuantum Reference
    (state.mapClassical placement.borrowedClassicalJoin)

/-- Complete borrowed reconstruction preserves the mass of the entire joint observation. -/
lemma contextEmbedding_reassembleBorrowed_mass (Reference : Register)
    (state : ExecutionState (localCtx.borrowedClassicalShape.Value × Store placement.frame)
      (localCtx.borrowedQuantumLayout.register.prod (placement.frame.register.prod Reference))) :
    (placement.reassembleBorrowed Reference state).mass = state.mass := by
  unfold reassembleBorrowed reassembleBorrowedQuantum ExecutionState.mass
  simp only [placement.contextEmbedding_reassembleBorrowedDensity_mass]
  exact state.mapClassical_mass _

private lemma split_borrowedLabels {Reference : Register} {H : Type} [Fintype H]
    (state : State caller Reference H) :
    ((placement.split state).mapClassical fun record =>
      (record.1.readBorrowedClassical, record.2.1)).mapClassical placement.borrowedClassicalJoin =
    (state.mapClassical fun record => record.1.readBorrowedClassical).reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference) := by
  rw [ExecutionState.executionState_mapClassical_comp, split,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  congr 2
  funext record
  exact placement.contextEmbedding_borrowedClassicalJoin_split record.1

/-- Caller borrowed restoration is determined by one joint local/frame/reference CQ observation. -/
lemma contextEmbedding_observeBorrowed_split
    {Reference : Register} {H : Type} [Fintype H] (state : State caller Reference H) :
    observeBorrowed Reference state =
      placement.reassembleBorrowed Reference
        (observeBorrowedTagged (Tag := placement.frameStoreTag) Prod.fst
          (placement.split state)) := by
  change borrowedQuantum caller Reference
    (state.mapClassical fun record => record.1.readBorrowedClassical) =
      placement.reassembleBorrowedQuantum Reference
        ((borrowedQuantum localCtx (placement.frame.register.prod Reference)
          ((placement.split state).mapClassical fun record =>
            (record.1.readBorrowedClassical, record.2.1))).mapClassical
          placement.borrowedClassicalJoin)
  rw [← borrowedQuantum_mapClassical, placement.split_borrowedLabels]
  apply ExecutionState.ext
  intro value
  exact placement.contextEmbedding_observeBorrowedWithReference Reference
    ((state.mapClassical fun record => record.1.readBorrowedClassical).block value)

end ContextEmbedding

end

end QuantumAlg
