/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Composition.Embedding
public import QuantumAlg.Core.Execution.State
public import QuantumAlg.Core.Base.Classical.Oracle.Composition
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
import all QuantumAlg.Core.Execution.Composition.Embedding
import all QuantumAlg.Core.Execution.Interpret.Preserving
import all QuantumAlg.Core.Execution.State.Coordinates
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Interpreter composition with independent persistent services

The interpreter supplies structurally recursive child interpretations. These
helpers only reorganize exact service-state coordinates and call those child
interpretations through their certified physical placements. They are not
instruction constructors and grant no replacement transition or query access.

Each child's inaccessible service component remains in its mathematical
history. Physical embedding independently retains every complement cell and
quantum system. No hidden state is copied, sampled, initialized or discarded.
-/

namespace QuantumAlg.Execution

noncomputable section

open ClassicalOracleModel

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {left right parent : ClassicalOracleModel} (join : ServiceJoin left right parent)

/-- Exact history coordinates with the left service active and the right state retained. -/
@[expose] public def serviceHistoryLeft (History : Type) :
    (parent.HiddenState × History) ≃ (left.HiddenState × (right.HiddenState × History)) :=
  (join.hidden.prodCongr (Equiv.refl History)).trans
    (Equiv.prodAssoc left.HiddenState right.HiddenState History)

/-- Exact history coordinates with the right service active and the left state retained. -/
@[expose] public def serviceHistoryRight (History : Type) :
    (parent.HiddenState × History) ≃ (right.HiddenState × (left.HiddenState × History)) :=
  ((join.hidden.trans (Equiv.prodComm left.HiddenState right.HiddenState)).prodCongr
    (Equiv.refl History)).trans
      (Equiv.prodAssoc right.HiddenState left.HiddenState History)

/-- The left child's newly produced path stays separate from its preserved history. -/
@[expose] public def serviceResultLeft (History Path : Type) :
    (parent.HiddenState × (History × Path)) ≃
      (left.HiddenState × ((right.HiddenState × History) × Path)) :=
  (serviceHistoryLeft join (History × Path)).trans
    ((Equiv.refl left.HiddenState).prodCongr
      (Equiv.prodAssoc right.HiddenState History Path).symm)

/-- The right child's newly produced path stays separate from its preserved history. -/
@[expose] public def serviceResultRight (History Path : Type) :
    (parent.HiddenState × (History × Path)) ≃
      (right.HiddenState × ((left.HiddenState × History) × Path)) :=
  (serviceHistoryRight join (History × Path)).trans
    ((Equiv.refl right.HiddenState).prodCongr
      (Equiv.prodAssoc left.HiddenState History Path).symm)

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {Reference : Register}
  {History Path : Type} [Fintype History] [Fintype Path]

open scoped Classical in
/-- Select the left service without changing any caller storage or quantum block. -/
@[expose] public def serviceInputLeft
    (state : State ctx Reference (parent.HiddenState × History)) :
    State ctx Reference (left.HiddenState × (right.HiddenState × History)) :=
  state.mapClassical ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryLeft join History))

open scoped Classical in
/-- Select the right service without changing any caller storage or quantum block. -/
@[expose] public def serviceInputRight
    (state : State ctx Reference (parent.HiddenState × History)) :
    State ctx Reference (right.HiddenState × (left.HiddenState × History)) :=
  state.mapClassical ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryRight join History))

open scoped Classical in
/-- Return the changed left state, preserved right state and complete path to the caller. -/
@[expose] public def serviceOutputLeft
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × History) × Path))) :
    State ctx Reference (parent.HiddenState × (History × Path)) :=
  state.mapClassical
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultLeft join History Path).symm)

open scoped Classical in
/-- Return the changed right state, preserved left state and complete path to the caller. -/
@[expose] public def serviceOutputRight
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × History) × Path))) :
    State ctx Reference (parent.HiddenState × (History × Path)) :=
  state.mapClassical
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultRight join History Path).symm)

/-- Left service selection retains the full subnormalized input mass. -/
public lemma serviceInputLeft_mass
    (state : State ctx Reference (parent.HiddenState × History)) :
    (serviceInputLeft join state).mass = state.mass := state.mapClassical_mass _

/-- Right service selection retains the full subnormalized input mass. -/
public lemma serviceInputRight_mass
    (state : State ctx Reference (parent.HiddenState × History)) :
    (serviceInputRight join state).mass = state.mass := state.mapClassical_mass _

/-- Rejoining a left result retains its full subnormalized output mass. -/
public lemma serviceOutputLeft_mass
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × History) × Path))) :
    (serviceOutputLeft join state).mass = state.mass := state.mapClassical_mass _

/-- Rejoining a right result retains its full subnormalized output mass. -/
public lemma serviceOutputRight_mass
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × History) × Path))) :
    (serviceOutputRight join state).mass = state.mass := state.mapClassical_mass _

/-- Selecting a left service retains each complete density block, not just its probability. -/
public lemma serviceInputLeft_block
    (state : State ctx Reference (parent.HiddenState × History))
    (value : Store ctx × (left.HiddenState × (right.HiddenState × History))) :
    (serviceInputLeft join state).block value =
      state.block (value.1, (serviceHistoryLeft join History).symm value.2) :=
  ExecutionState.coordinate_mapClassical_block state
    ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryLeft join History)) value

/-- Selecting a right service retains each complete density block and reference correlation. -/
public lemma serviceInputRight_block
    (state : State ctx Reference (parent.HiddenState × History))
    (value : Store ctx × (right.HiddenState × (left.HiddenState × History))) :
    (serviceInputRight join state).block value =
      state.block (value.1, (serviceHistoryRight join History).symm value.2) :=
  ExecutionState.coordinate_mapClassical_block state
    ((Equiv.refl (Store ctx)).prodCongr (serviceHistoryRight join History)) value

/-- Returning a left result retains the exact changed service and quantum/reference block. -/
public lemma serviceOutputLeft_block
    (state : State ctx Reference (left.HiddenState × ((right.HiddenState × History) × Path)))
    (value : Store ctx × (parent.HiddenState × (History × Path))) :
    (serviceOutputLeft join state).block value =
      state.block (value.1, serviceResultLeft join History Path value.2) :=
  ExecutionState.coordinate_mapClassical_block state
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultLeft join History Path).symm) value

/-- Returning a right result retains the exact changed service and quantum/reference block. -/
public lemma serviceOutputRight_block
    (state : State ctx Reference (right.HiddenState × ((left.HiddenState × History) × Path)))
    (value : Store ctx × (parent.HiddenState × (History × Path))) :
    (serviceOutputRight join state).block value =
      state.block (value.1, serviceResultRight join History Path value.2) :=
  ExecutionState.coordinate_mapClassical_block state
    ((Equiv.refl (Store ctx)).prodCongr (serviceResultRight join History Path).symm) value

/-- Run a supplied left interpretation with the other service state inaccessible in history. -/
def serviceLeftPreserving
    (body : Preserving left.HiddenState ctx ctx Reference Path) :
    Preserving parent.HiddenState ctx ctx Reference Path := fun state =>
  let first := serviceInputLeft join state
  let result := body first
  ⟨serviceOutputLeft join result.val,
    (serviceOutputLeft_mass join result.val).trans
      (result.property.trans (serviceInputLeft_mass join state))⟩

/-- Run a supplied right interpretation with the other service state inaccessible in history. -/
def serviceRightPreserving
    (body : Preserving right.HiddenState ctx ctx Reference Path) :
    Preserving parent.HiddenState ctx ctx Reference Path := fun state =>
  let first := serviceInputRight join state
  let result := body first
  ⟨serviceOutputRight join result.val,
    (serviceOutputRight_mass join result.val).trans
      (result.property.trans (serviceInputRight_mass join state))⟩

/-- Physical placement and left-service selection preserve both inaccessible complements. -/
def embedServiceLeftPreserving {localCtx caller : RuntimeCtx kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Preserving left.HiddenState localCtx localCtx
      (Register.prod placement.frame.register Reference) Path) :
    Preserving parent.HiddenState caller caller Reference Path :=
  serviceLeftPreserving join (embedPreserving placement Reference body)

/-- Physical placement and right-service selection preserve both inaccessible complements. -/
def embedServiceRightPreserving {localCtx caller : RuntimeCtx kind}
    (placement : ContextEmbedding localCtx caller)
    (body : Preserving right.HiddenState localCtx localCtx
      (Register.prod placement.frame.register Reference) Path) :
    Preserving parent.HiddenState caller caller Reference Path :=
  serviceRightPreserving join (embedPreserving placement Reference body)

/-- Interpret the two disjoint children in order, retaining their complete pair of paths. -/
def parallelPreserving {leftCtx rightCtx : RuntimeCtx kind}
    (separate : RuntimeCtx.StorageDisjoint leftCtx rightCtx)
    {LeftPath RightPath : Type} [Fintype LeftPath] [Fintype RightPath]
    (first : Preserving left.HiddenState leftCtx leftCtx
      (Register.prod rightCtx.register Reference) LeftPath)
    (second : Preserving right.HiddenState rightCtx rightCtx
      (Register.prod leftCtx.register Reference) RightPath) :
    Preserving parent.HiddenState (leftCtx.disjointUnion rightCtx separate)
      (leftCtx.disjointUnion rightCtx separate) Reference (LeftPath × RightPath) := fun state =>
  let leftResult := embedServiceLeftPreserving join
    (ContextEmbedding.alongUnion leftCtx rightCtx separate) first state
  let rightResult := embedServiceRightPreserving join
    (ContextEmbedding.alongUnionRight leftCtx rightCtx separate) second leftResult.val
  ⟨rightResult.val.mapClassical (fun record =>
      (record.1, (record.2.1, (record.2.2.1.1, (record.2.2.1.2, record.2.2.2))))),
    (rightResult.val.mapClassical_mass _).trans
      (rightResult.property.trans leftResult.property)⟩

end

end QuantumAlg.Execution
