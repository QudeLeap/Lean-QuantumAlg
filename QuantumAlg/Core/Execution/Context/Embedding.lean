/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context.Embedding
public import QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Base.Accounting.Context.Embedding
import all QuantumAlg.Core.Execution.Context.Permutation.Layout
import all QuantumAlg.Core.Execution.Context.Permutation.Store
import all QuantumAlg.Core.Execution.Context.Relabeling.Layout
import all QuantumAlg.Core.Execution.Context.Relabeling.Store
import all QuantumAlg.Core.Execution.Context.Union.Basis
import all QuantumAlg.Core.Execution.Context.Union.Store
import all QuantumAlg.Core.Execution.State.Coordinate.Transport
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Exact state coordinates for an embedded execution

The complete caller is split along its certified physical placement. Every
complement wire remains in the quantum reference and every complement cell
remains in the classical history. The coordinate changes are inverse on the
full classical-quantum state, including arbitrary correlations and impossible
branches [dW19, qcnotes.tex:389,5381,5394]. They execute no quantum operation.
-/

namespace QuantumAlg.ContextEmbedding

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller)

/-- Read each physical value through relabeling, union placement and entry order. -/
public def basis : caller.register.Index ≃
    localCtx.register.Index × placement.frame.register.Index :=
  (ContextPermutation.basis placement.covers).symm.trans
    ((ContextUnion.unionBasisEquiv (localCtx.relabel placement.keys placement.physical)
      placement.frame placement.separate).trans
        ((ContextRelabeling.basis localCtx placement.keys placement.physical).symm.prodCongr
          (Equiv.refl placement.frame.register.Index)))

/-- The complete finite store is retained, with every cell on its original side. -/
public def store : Store caller ≃ Store localCtx × Store placement.frame :=
  (ContextPermutation.storeEquiv placement.covers).symm.trans
    ((ContextUnion.storeEquiv placement.separate).trans
      ((ContextRelabeling.storeEquiv placement.keys placement.physical localCtx).symm.prodCongr
        (Equiv.refl (Store placement.frame))))

/-- Keep the complement beside the original external reference, without marginalizing it. -/
public def referenceBasis (Reference : Register) :
    (Register.prod caller.register Reference).Index ≃
      (Register.prod localCtx.register (Register.prod placement.frame.register Reference)).Index :=
  ((placement.basis).prodCongr (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc localCtx.register.Index placement.frame.register.Index Reference.Index)

/-- Preserve the complement's full stored value beside the mathematical history. -/
public def record (History : Type) :
    (Store caller × History) ≃ (Store localCtx × (Store placement.frame × History)) :=
  ((placement.store).prodCongr (Equiv.refl History)).trans
    (Equiv.prodAssoc (Store localCtx) (Store placement.frame) History)

variable {Reference : Register} {History : Type} [Fintype History]

/-- Expose only the local live context to a child, retaining the complete caller state. -/
public def split (state : State caller Reference History) :
    State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × History) :=
  (state.mapClassical (placement.record History)).reindex (placement.referenceBasis Reference)

/-- Restore the original caller coordinates after the child's context-preserving execution. -/
public def join
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × History)) : State caller Reference History :=
  (state.mapClassical (placement.record History).symm).reindex
    (placement.referenceBasis Reference).symm

/-- Splitting and rejoining retain every joint state block exactly. -/
public lemma contextEmbedding_join_split (state : State caller Reference History) :
    placement.join (placement.split state) = state :=
  ExecutionState.coordinate_transport_inverse state (placement.record History)
    (placement.referenceBasis Reference)

/-- The same inverse law holds for arbitrary correlated local and complement coordinates. -/
public lemma contextEmbedding_split_join
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × History)) : placement.split (placement.join state) = state :=
  ExecutionState.coordinate_transport_inverse state (placement.record History).symm
    (placement.referenceBasis Reference).symm

/-- Splitting does not normalize or discard a classical branch. -/
public lemma contextEmbedding_split_mass (state : State caller Reference History) :
    (placement.split state).mass = state.mass :=
  (ExecutionState.reindex_mass _ _).trans (ExecutionState.mapClassical_mass _ _)

/-- Rejoining preserves the total weight of every child result. -/
public lemma contextEmbedding_join_mass
    (state : State localCtx (Register.prod placement.frame.register Reference)
      (Store placement.frame × History)) : (placement.join state).mass = state.mass :=
  (ExecutionState.reindex_mass _ _).trans (ExecutionState.mapClassical_mass _ _)

/-- The coordinate map preserves each matrix entry, rather than only its marginal. -/
public lemma contextEmbedding_split_entry (state : State caller Reference History)
    (label : Store localCtx × (Store placement.frame × History))
    (row column :
      (Register.prod localCtx.register (Register.prod placement.frame.register Reference)).Index) :
    ((placement.split state).block label).matrix row column =
      (state.block ((placement.record History).symm label)).matrix
        ((placement.referenceBasis Reference).symm row)
        ((placement.referenceBasis Reference).symm column) :=
  ExecutionState.coordinate_transport_entry state (placement.record History)
    (placement.referenceBasis Reference) label row column

/-- The caller's resident resources include the entire local context and its complement. -/
public lemma contextEmbedding_resident_space :
    caller.residentSpace = localCtx.residentSpace + placement.frame.residentSpace := by
  rw [← ContextPermutation.resident_space placement.covers,
    RuntimeCtx.residentSpace_disjointUnion, RuntimeCtx.relabel_residentSpace]

/-- Storage roles are preserved, so auxiliary resources obey the same exact accounting. -/
public lemma contextEmbedding_auxiliary_space :
    caller.auxiliarySpace = localCtx.auxiliarySpace + placement.frame.auxiliarySpace := by
  rw [← ContextPermutation.auxiliary_space placement.covers,
    RuntimeCtx.auxiliarySpace_disjointUnion, RuntimeCtx.relabel_auxiliarySpace]

end

end QuantumAlg.ContextEmbedding
