/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Batch.Slots
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Reference-aware frame of fixed EH sample allocation

Allocating sample and factor cells leaves every earlier source and parameter
value, including its external-reference matrix coefficient, intact. This
generic statement serves both query models using the same storage layout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Slots

open Execution

noncomputable section

/-- Lift a structural read through actual sample-cell allocations. -/
def slotsInput {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (width : Nat) (input : CInputRef ctx shape) :
    (count : Nat) → CInputRef (samples ctx width count) shape
  | 0 => input
  | count + 1 => (slotsInput width input count).underRetained
      (samples ctx width count).canonicalFreshKey (.bits width)
      (samples ctx width count).canonicalFreshKey_fresh

lemma slotsInput_storage {kind : ProblemKind} {ctx : RuntimeCtx kind} {shape : CShape}
    (width : Nat) (ref : CWriteRef ctx shape) (count : Nat) :
    slotsInput width (.storage ref.toCStorageRef) count =
      .storage (liftSamples width ref count).toCStorageRef := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact congrArg
        (fun read : CInputRef (samples ctx width count) shape => read.underRetained
          (samples ctx width count).canonicalFreshKey (.bits width)
          (samples ctx width count).canonicalFreshKey_fresh) ih

lemma slotsInput_product {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {left right : CShape} (width : Nat) (first : CInputRef ctx left)
    (second : CInputRef ctx right) (count : Nat) :
    slotsInput width (.product first second) count =
      .product (slotsInput width first count) (slotsInput width second count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact congrArg
        (fun read : CInputRef (samples ctx width count) (.product left right) =>
          read.underRetained (samples ctx width count).canonicalFreshKey (.bits width)
            (samples ctx width count).canonicalFreshKey_fresh) ih

/-- The finite sequence of actual retention instructions preserves weighted
reference-fiber observations of every pre-existing structural read. -/
lemma allocateSamples_reference {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment}
    (ctx : RuntimeCtx .quantum) (width : Nat) {shape : CShape}
    (input : CInputRef ctx shape)
    (count : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((allocateSamples (model := .quantum gates oracles operations classicalOracles)
        ctx width count).execute environment Reference state)
      (fun entry _ => weight (entry.1.read (slotsInput width input count))) leftRef rightRef =
    ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
      leftRef rightRef := by
  induction count with
  | zero =>
      have executed := congrArg
        (fun output : State ctx Reference
          (classicalOracles.HiddenState × (History × Unit)) =>
          ExecutionState.referenceFiberSum output
            (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
        (Circuit.execute_id_mapClassical (environment := environment) (allowAllocation := true)
          (model := .quantum gates oracles operations classicalOracles) Reference state)
      exact executed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight (entry.1.read input)) leftRef rightRef)
  | succ count ih =>
      let previous := allocateSamples
        (model := .quantum gates oracles operations classicalOracles) ctx width count
      let retained := Circuit.retain
        (model := .quantum gates oracles operations classicalOracles) (samples ctx width count)
        (samples ctx width count).canonicalFreshKey (.bits width)
        (samples ctx width count).canonicalFreshKey_fresh
      exact (Circuit.referenceFiberSum_execute_seq (environment := environment) previous
        retained state
        (fun store => weight (store.read (slotsInput width input (count + 1))))
        leftRef rightRef).trans
        ((Circuit.referenceFiberSum_execute_retain_input (environment := environment)
          (slotsInput width input count)
          (samples ctx width count).canonicalFreshKey (.bits width)
          (samples ctx width count).canonicalFreshKey_fresh
          (previous.execute environment Reference state) weight leftRef rightRef).trans ih)

attribute [local irreducible] samples allocateSamples liftSamples

/-- Retaining all sixteen samples and the factor cell leaves the joint value
of any two previously existing cells unchanged in every reference block. -/
lemma allocate_pair_reference {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
    {environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment}
    (ctx : RuntimeCtx .quantum) (N : Nat)
    {firstShape secondShape : CShape}
    (first : CWriteRef ctx firstShape) (second : CWriteRef ctx secondShape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : firstShape.Value → secondShape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((allocate (model := .quantum gates oracles operations classicalOracles)
        ctx N).execute environment Reference state)
      (fun entry _ => weight
        (entry.1.read (.storage (liftWrite N first).toCStorageRef))
        (entry.1.read (.storage (liftWrite N second).toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight
        (entry.1.read (.storage first.toCStorageRef))
        (entry.1.read (.storage second.toCStorageRef))) leftRef rightRef := by
  let oldRead := CInputRef.product (.storage first.toCStorageRef) (.storage second.toCStorageRef)
  let oldWeight := fun value : (CShape.product firstShape secondShape).Value =>
    weight value.first value.second
  let previous := allocateSamples
    (model := .quantum gates oracles operations classicalOracles)
    ctx (measurementBits N) 16
  let middle := samples ctx (measurementBits N) 16
  let factor := Circuit.retain
    (model := .quantum gates oracles operations classicalOracles)
    middle middle.canonicalFreshKey
    (.option (.unsignedWord (modulusBits N))) middle.canonicalFreshKey_fresh
  have lifted : slotsInput (measurementBits N) oldRead 16 =
      .product (.storage (liftSamples (measurementBits N) first 16).toCStorageRef)
        (.storage (liftSamples (measurementBits N) second 16).toCStorageRef) :=
    (slotsInput_product (measurementBits N) _ _ 16).trans
      (congrArg₂ CInputRef.product (slotsInput_storage _ first 16)
        (slotsInput_storage _ second 16))
  have kept := Circuit.referenceFiberSum_execute_retain_input (environment := environment)
    (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles)
    (.product (.storage (liftSamples (measurementBits N) first 16).toCStorageRef)
      (.storage (liftSamples (measurementBits N) second 16).toCStorageRef))
    middle.canonicalFreshKey (.option (.unsignedWord (modulusBits N)))
    middle.canonicalFreshKey_fresh (previous.execute environment Reference state) oldWeight
      leftRef rightRef
  have oldSlots := allocateSamples_reference (environment := environment)
    (gates := gates) (oracles := oracles)
    (operations := operations) (classicalOracles := classicalOracles)
    ctx (measurementBits N) oldRead 16 state oldWeight leftRef rightRef
  have observed := congrArg
    (fun read : CInputRef middle (.product firstShape secondShape) =>
      ExecutionState.referenceFiberSum (previous.execute environment Reference state)
        (fun entry _ => oldWeight (entry.1.read read)) leftRef rightRef) lifted
  exact (Circuit.referenceFiberSum_execute_seq (environment := environment) previous factor state
    (fun store => weight (store.read (.storage (liftWrite N first).toCStorageRef))
      (store.read (.storage (liftWrite N second).toCStorageRef))) leftRef rightRef).trans
        (kept.trans (observed.symm.trans oldSlots))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Batch.Slots
