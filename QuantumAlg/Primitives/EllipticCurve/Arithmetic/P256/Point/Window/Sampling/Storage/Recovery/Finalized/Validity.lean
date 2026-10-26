/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Validity
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Finalized
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Validity
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop

/-! # Selected scalar range through the actual finalized recovery run -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
namespace Storage

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

noncomputable section
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma cleanup_selected_lt {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (cleanup : Cleanup.Parameters ctx) (selected : CStorageRef ctx (.unsignedWord 260))
    (bound : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage selected)).toNat < bound) :
    ∀ entry, 0 < (((Circuit.embed (allowAllocation := true)
      (ContextEmbedding.identity ctx) cleanup.circuit).execute environment Reference state).block
      entry).mass →
      (entry.1.read (.storage selected)).toNat < bound := by
  have selectedRead : SelectsRead
      (originalStorageRead selected (fun value => decide (value.toNat < bound))) true
      (Circuit.embed (allowAllocation := true)
        (ContextEmbedding.identity ctx) cleanup.circuit) environment := by
    apply selects_read_identity_embed
    exact reset_selects_storage cleanup ctx.systemCount id selected
      (fun value => decide (value.toNat < bound)) true
      (by intro cardinality impossible; cases impossible) environment
  have preserved := selects_read_preserves_positive
    (originalStorageRead selected (fun value => decide (value.toNat < bound))) true
    (Circuit.embed (allowAllocation := true)
      (ContextEmbedding.identity ctx) cleanup.circuit) environment selectedRead
    state (fun entry positive => decide_eq_true (supported entry positive))
  intro entry positive
  exact of_decide_eq_true (preserved entry positive)

private def PreservesBound {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (input : CInputRef ctx (.unsignedWord 260)) (bound : Nat)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    (∀ entry, 0 < (state.block entry).mass → (entry.1.read input).toNat < bound) →
    ∀ entry, 0 < ((code.execute environment Reference state).block entry).mass →
      (entry.1.read input).toNat < bound

private lemma workspace_preserves_bound {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (input : CInputRef ctx (.unsignedWord 260)) (bound : Nat)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (ctx.addWorkspace key shape fresh) (ctx.addWorkspace key shape fresh))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (preserved : PreservesBound (input.underWorkspace key shape fresh) bound body environment) :
    PreservesBound input bound
      (Circuit.workspace (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx key shape fresh body) environment := by
  intro Reference History finite state supported
  have allocated : ∀ entry, 0 < ((state.pushWorkspace key shape fresh).block entry).mass →
      (entry.1.read (input.underWorkspace key shape fresh)).toNat < bound := by
    rw [State.state_pushWorkspace_as_mapClassical]
    apply Conditional.mapped_supported
    · exact supported
    · intro entry prior
      simpa only [Store.read_pushWorkspace_underWorkspace] using prior
  rw [Circuit.execute_workspace]
  unfold State.popWorkspace
  apply Conditional.mapped_supported
  · exact preserved (state.pushWorkspace key shape fresh) allocated
  · intro entry prior
    simpa only [Store.read_popWorkspace_underWorkspace] using prior

private lemma withFrame_preserves_bound {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (input : CInputRef ctx (.unsignedWord 260)) (bound : Nat)
    (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (scratch : Frame inner wordWidth parityCount) → CallerFree scratch lift →
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (preserved : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (scratch : Frame inner wordWidth parityCount) (fresh : CallerFree scratch lift),
      PreservesBound (lift.liftInput input) bound (body lift same scratch fresh) environment) :
    PreservesBound input bound
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := by
  have actual : PreservesBound ((Transport.id ctx).liftInput input) bound
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (Transport.id ctx) rfl
    (shapes wordWidth parityCount)
    (fun cells distinct lift separated same =>
      body lift (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct lift separated))
    (fun lift _ code => PreservesBound (lift.liftInput input) bound code environment)
    (by
      intro inner lift same key shape fresh code established
      apply workspace_preserves_bound (lift.liftInput input) bound key shape fresh code environment
      intro Reference History finite state
      have returned := @established Reference History finite state
      simpa only [Transport.liftInput_underWorkspace] using returned)
    (by
      intro inner cells distinct lift separated same Reference History finite state supported
      exact @preserved inner lift (quantumLayout_wires_of_quantumWires same)
        (Frame.ofCells cells distinct) (ofCells_callerFree cells distinct lift separated)
        Reference History finite state supported)
  intro Reference History finite state
  have returned := @actual Reference History finite state
  simpa only [Transport.liftInput_id] using returned

namespace Inputs

private def FinalizedInnerSelectedLtStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (inputs : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx) (count : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (_distinct : checkers.keys.Nodup)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < inputs.order.modulus),
    ∀ entry, 0 < (((inputs.finalizedInnerBody sampler checkers count).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < inputs.order.modulus

private lemma finalizedInnerSelectedLt_proof : FinalizedInnerSelectedLtStatement := by
  intro ctx services inputs sampler checkers count environment distinct
    Reference History finite state supported
  apply Circuit.supported_store_seq environment
    (Circuit.forRange count fun _ => inputs.attempt (services := services) sampler checkers)
    (Circuit.embed (ContextEmbedding.identity ctx) (finalizedCleanup sampler).circuit)
    Reference state
    (fun store => (store.read (.storage checkers.selected.toCStorageRef)).toNat <
      inputs.order.modulus)
  apply cleanup_selected_lt (ctx := ctx) (services := services)
    (finalizedCleanup sampler) checkers.selected.toCStorageRef
    inputs.order.modulus environment
  exact preservesStore_forRange (environment := environment) count
    (fun _ => inputs.attempt (services := services) sampler checkers)
    (fun store => (store.read (.storage checkers.selected.toCStorageRef)).toNat <
      inputs.order.modulus)
    (by
      intro index Reference History finite current prior
      exact inputs.attempt_selected_lt (services := services) sampler checkers environment
        distinct current prior)
    state supported

/-- All real attempts and terminal measured cleanup preserve the original scalar range. -/
lemma finalizedInnerBody_selected_lt {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (inputs : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx) (count : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (distinct : checkers.keys.Nodup)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < inputs.order.modulus) :
    ∀ entry, 0 < (((inputs.finalizedInnerBody sampler checkers count).execute
      environment Reference state).block entry).mass →
      (entry.1.read (.storage checkers.selected.toCStorageRef)).toNat < inputs.order.modulus := by
  exact finalizedInnerSelectedLt_proof (ctx := ctx) (services := services) inputs sampler checkers
    count environment distinct (Reference := Reference) (History := History) state supported

attribute [local irreducible] withFrame

/-- Lexical feedback allocation and release retain the original selected-word range. -/
lemma scopedAttemptsFinalized_selected_lt {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx) (count : Nat)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) :
    PreservesBound (.storage (Checkers.retained ctx).selected.toCStorageRef)
      original.order.modulus (original.scopedAttemptsFinalized count) environment := by
  unfold scopedAttemptsFinalized
  exact withFrame_preserves_bound (ctx := persistentCtx ctx 256 260) (services := services)
    (.storage (Checkers.retained ctx).selected.toCStorageRef) original.order.modulus 256 256
    (fun lift same scratch fresh =>
      (original.currentInput lift same).finalizedInnerBody (services := services)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift) count)
    environment (by
      intro inner lift same scratch fresh Reference History finite state supported
      exact finalizedInnerBody_selected_lt (ctx := inner) (services := services)
        (original.currentInput lift same)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift) count environment
        (Checkers.transport_retained_keys_nodup lift) state supported)

private lemma retained_selected_lt {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (bound : Nat) (positiveBound : 0 < bound)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ∀ entry, 0 < (((retainPersistent
      (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260).execute
        environment Reference state).block entry).mass →
      (entry.1.read (.storage (Checkers.retained ctx).selected.toCStorageRef)).toNat < bound := by
  intro entry positive
  have initial := retainPersistent_latches_supported
    (environment := environment) 256 260 state entry positive
  change (entry.1.read (.storage (persistentSelected ctx 256 260).toCStorageRef)).toNat < _
  rw [initial.2]
  simp only [CShape.initialValue, CShape.wordOfNat_val, Nat.zero_mod]
  exact positiveBound

private def RunFinalizedSomeLtStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)),
    ∀ entry, 0 < (((original.runFinalized (services := services)).code.execute
      environment Reference state).block entry).mass →
      ∀ value, entry.1.read (batchResultRead ctx 256 260) = .optionSome value →
        value.toNat < original.order.modulus

private lemma runFinalizedSomeLt_proof : RunFinalizedSomeLtStatement := by
  intro ctx services original environment Reference History finite state
  let retained := retainPersistent
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) ctx 256 260
  let loop := original.scopedAttemptsFinalized (services := services) 3
  have retainedBound := retained_selected_lt (ctx := ctx) (services := services)
    original.order.modulus (lt_of_lt_of_le (by decide : 0 < 2) original.order.two_le)
    environment state
  have prefixBound := Circuit.supported_store_seq environment retained loop Reference state
    (fun store => (store.read (.storage (Checkers.retained ctx).selected.toCStorageRef)).toNat <
      original.order.modulus)
    (original.scopedAttemptsFinalized_selected_lt (services := services) 3 environment
      (retained.execute environment Reference state) retainedBound)
  apply Circuit.supported_store_seq environment (retained.seq loop)
    (packBatchResult (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      ctx 256 260) Reference state
    (fun store => ∀ value, store.read (batchResultRead ctx 256 260) = .optionSome value →
      value.toNat < original.order.modulus)
  intro entry positive value output
  exact packBatchResult_supported_property (environment := environment)
    (fun value => value.toNat < original.order.modulus)
    ((retained.seq loop).execute environment Reference state)
    (fun before present _ => prefixBound before present) entry positive value output

/-- Any present actual finalized result carries a scalar below the original order. -/
lemma runFinalized_some_lt {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ∀ entry, 0 < (((original.runFinalized (services := services)).code.execute
      environment Reference state).block entry).mass →
      ∀ value, entry.1.read (batchResultRead ctx 256 260) = .optionSome value →
        value.toNat < original.order.modulus := by
  exact runFinalizedSomeLt_proof (ctx := ctx) (services := services) original environment
    (Reference := Reference) (History := History) state

end Inputs
end
end Storage
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
