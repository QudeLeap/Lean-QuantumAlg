/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Classical.Oracle

/-!
# Closed composition of independent classical services

A service join either retains both independent hidden states or omits an empty
grant. It cannot identify mutable states, initialize a state, change a declared
transition, or implement a query by an unaccounted conversion. In particular,
combining two empty grants keeps the empty model itself.

The hidden-state equivalence also applies to correlated input states. It only
regroups existing information; it makes no probabilistic independence claim.
-/

namespace QuantumAlg.ClassicalOracleModel

noncomputable section

/-- Independent sum or omission of an empty grant, with no arbitrary conversions. -/
public inductive ServiceJoin : ClassicalOracleModel → ClassicalOracleModel →
    ClassicalOracleModel → Type 1 where
  | sum (left right : ClassicalOracleModel) : ServiceJoin left right (.sum left right)
  | leftEmpty (right : ClassicalOracleModel) : ServiceJoin .empty right right
  | rightEmpty (left : ClassicalOracleModel) : ServiceJoin left .empty left

namespace ServiceJoin

variable {left right parent : ClassicalOracleModel}

/-- Restrict an environment to the existing left service, without changing its law. -/
@[expose, implicit_reducible]
public def interpretationLeft (join : ServiceJoin left right parent)
    (environment : parent.Interpretation) : left.Interpretation :=
  match join with
  | .sum _ _ => environment.1
  | .leftEmpty _ => ()
  | .rightEmpty _ => environment

/-- Restrict an environment to the existing right service, without changing its law. -/
@[expose, implicit_reducible]
public def interpretationRight (join : ServiceJoin left right parent)
    (environment : parent.Interpretation) : right.Interpretation :=
  match join with
  | .sum _ _ => environment.2
  | .leftEmpty _ => environment
  | .rightEmpty _ => ()

/-- Split the persistent service state without sampling or initialization. -/
public def hidden (join : ServiceJoin left right parent) :
    parent.HiddenState ≃ (left.HiddenState × right.HiddenState) :=
  match join with
  | .sum _ _ => Equiv.refl _
  | .leftEmpty _ =>
      { toFun := fun state => ((), state)
        invFun := Prod.snd
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨⟨⟩, state⟩; rfl }
  | .rightEmpty _ =>
      { toFun := fun state => (state, ())
        invFun := Prod.fst
        left_inv := fun _ => rfl
        right_inv := by rintro ⟨state, ⟨⟩⟩; rfl }

/-- Inject exactly a granted left query into the parent declaration. -/
public def queryLeft : ServiceJoin left right parent → left.Query → parent.Query
  | .sum _ _ => Sum.inl
  | .leftEmpty _ => Empty.elim
  | .rightEmpty _ => id

/-- Inject exactly a granted right query into the parent declaration. -/
public def queryRight : ServiceJoin left right parent → right.Query → parent.Query
  | .sum _ _ => Sum.inr
  | .leftEmpty _ => id
  | .rightEmpty _ => Empty.elim

/-- Route the left declaration's actual event coordinate. -/
public def coordinateLeft : ServiceJoin left right parent → left.Coordinate → parent.Coordinate
  | .sum _ _ => Sum.inl
  | .leftEmpty _ => Empty.elim
  | .rightEmpty _ => id

/-- Route the right declaration's actual event coordinate. -/
public def coordinateRight : ServiceJoin left right parent → right.Coordinate → parent.Coordinate
  | .sum _ _ => Sum.inr
  | .leftEmpty _ => id
  | .rightEmpty _ => Empty.elim

/-- Joining empty grants does not change the execution model. -/
public def emptyJoin : ServiceJoin .empty .empty .empty := .leftEmpty .empty

/-- Splitting and joining retains the entire original hidden state. -/
public lemma serviceJoin_hidden_roundtrip
    (join : ServiceJoin left right parent) (state : parent.HiddenState) :
    join.hidden.symm (join.hidden state) = state := join.hidden.symm_apply_apply state

/-- A left query retains its declaration-owned operand shape. -/
public lemma serviceJoin_inputShape_left
    (join : ServiceJoin left right parent) (query : left.Query) :
    parent.inputShape (join.queryLeft query) = left.inputShape query := by
  cases join with
  | sum => rfl
  | leftEmpty => exact Empty.elim query
  | rightEmpty => rfl

/-- A left query retains its declaration-owned result shape. -/
public lemma serviceJoin_outputShape_left
    (join : ServiceJoin left right parent) (query : left.Query) :
    parent.outputShape (join.queryLeft query) = left.outputShape query := by
  cases join with
  | sum => rfl
  | leftEmpty => exact Empty.elim query
  | rightEmpty => rfl

/-- A right query retains its declaration-owned operand shape. -/
public lemma serviceJoin_inputShape_right
    (join : ServiceJoin left right parent) (query : right.Query) :
    parent.inputShape (join.queryRight query) = right.inputShape query := by
  cases join with
  | sum => rfl
  | leftEmpty => rfl
  | rightEmpty => exact Empty.elim query

/-- A right query retains its declaration-owned result shape. -/
public lemma serviceJoin_outputShape_right
    (join : ServiceJoin left right parent) (query : right.Query) :
    parent.outputShape (join.queryRight query) = right.outputShape query := by
  cases join with
  | sum => rfl
  | leftEmpty => rfl
  | rightEmpty => exact Empty.elim query

/-- The operand identification is the identity in every inhabited case. -/
public def inputLeft (join : ServiceJoin left right parent) (query : left.Query) :
    (left.inputShape query).Value ≃ (parent.inputShape (join.queryLeft query)).Value := by
  cases join with
  | sum => exact Equiv.refl _
  | leftEmpty => exact Empty.elim query
  | rightEmpty => exact Equiv.refl _

/-- The result identification is the identity in every inhabited case. -/
public def outputLeft (join : ServiceJoin left right parent) (query : left.Query) :
    (left.outputShape query).Value ≃ (parent.outputShape (join.queryLeft query)).Value := by
  cases join with
  | sum => exact Equiv.refl _
  | leftEmpty => exact Empty.elim query
  | rightEmpty => exact Equiv.refl _

/-- The operand identification is the identity in every inhabited case. -/
public def inputRight (join : ServiceJoin left right parent) (query : right.Query) :
    (right.inputShape query).Value ≃ (parent.inputShape (join.queryRight query)).Value := by
  cases join with
  | sum => exact Equiv.refl _
  | leftEmpty => exact Equiv.refl _
  | rightEmpty => exact Empty.elim query

/-- The result identification is the identity in every inhabited case. -/
public def outputRight (join : ServiceJoin left right parent) (query : right.Query) :
    (right.outputShape query).Value ≃ (parent.outputShape (join.queryRight query)).Value := by
  cases join with
  | sum => exact Equiv.refl _
  | leftEmpty => exact Equiv.refl _
  | rightEmpty => exact Empty.elim query

/-- The injected query emits the injected left event coordinate. -/
public lemma serviceJoin_coordinate_queryLeft
    (join : ServiceJoin left right parent) (query : left.Query) :
    parent.coordinate (join.queryLeft query) = join.coordinateLeft (left.coordinate query) := by
  cases join with
  | sum => rfl
  | leftEmpty => exact Empty.elim query
  | rightEmpty => rfl

/-- The injected query emits the injected right event coordinate. -/
public lemma serviceJoin_coordinate_queryRight
    (join : ServiceJoin left right parent) (query : right.Query) :
    parent.coordinate (join.queryRight query) = join.coordinateRight (right.coordinate query) := by
  cases join with
  | sum => rfl
  | leftEmpty => rfl
  | rightEmpty => exact Empty.elim query

/-- Distinct left coordinates remain distinct after routing. -/
public lemma serviceJoin_coordinateLeft_injective (join : ServiceJoin left right parent) :
    Function.Injective join.coordinateLeft := by
  cases join with
  | sum => exact Sum.inl_injective
  | leftEmpty => intro coordinate; exact Empty.elim coordinate
  | rightEmpty => exact Function.injective_id

/-- Distinct right coordinates remain distinct after routing. -/
public lemma serviceJoin_coordinateRight_injective (join : ServiceJoin left right parent) :
    Function.Injective join.coordinateRight := by
  cases join with
  | sum => exact Sum.inr_injective
  | leftEmpty => exact Function.injective_id
  | rightEmpty => intro coordinate; exact Empty.elim coordinate

/-- The two services cannot emit the same routed query coordinate. -/
public lemma serviceJoin_coordinates_disjoint (join : ServiceJoin left right parent)
    (leftCoordinate : left.Coordinate) (rightCoordinate : right.Coordinate) :
    join.coordinateLeft leftCoordinate ≠ join.coordinateRight rightCoordinate := by
  cases join with
  | sum => exact Sum.inl_ne_inr
  | leftEmpty => exact Empty.elim leftCoordinate
  | rightEmpty => exact Empty.elim rightCoordinate

/-- A left query updates only its existing component and carries the other state unchanged. -/
public lemma serviceJoin_transition_left
    (join : ServiceJoin left right parent) (environment : parent.Interpretation)
    (query : left.Query) (state : parent.HiddenState) (input : (left.inputShape query).Value) :
    parent.transition environment (join.queryLeft query) state (join.inputLeft query input) =
      (left.transition (join.interpretationLeft environment) query
        (join.hidden state).1 input).map fun result =>
          (join.hidden.symm (result.1, (join.hidden state).2), join.outputLeft query result.2) := by
  cases join with
  | sum => rfl
  | leftEmpty => exact Empty.elim query
  | rightEmpty left =>
      change left.transition environment query state input =
        (left.transition environment query state input).map id
      exact (PMF.map_id _).symm

/-- A right query updates only its existing component and carries the other state unchanged. -/
public lemma serviceJoin_transition_right
    (join : ServiceJoin left right parent) (environment : parent.Interpretation)
    (query : right.Query) (state : parent.HiddenState) (input : (right.inputShape query).Value) :
    parent.transition environment (join.queryRight query) state (join.inputRight query input) =
      (right.transition (join.interpretationRight environment) query
        (join.hidden state).2 input).map fun result =>
          (join.hidden.symm ((join.hidden state).1, result.1),
            join.outputRight query result.2) := by
  cases join with
  | sum => rfl
  | leftEmpty right =>
      change right.transition environment query state input =
        (right.transition environment query state input).map id
      exact (PMF.map_id _).symm
  | rightEmpty => exact Empty.elim query

end ServiceJoin

end

end QuantumAlg.ClassicalOracleModel
