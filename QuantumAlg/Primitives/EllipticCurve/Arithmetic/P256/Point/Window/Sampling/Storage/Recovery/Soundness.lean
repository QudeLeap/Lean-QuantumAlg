/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Validity
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First.Loop

/-! # Sound first-success latches through the actual recovery attempt -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
namespace Storage

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

noncomputable section
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private def SelectsReadPreservesImplicationStatement : Prop :=
  ∀
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (read : Store ctx → Bool) (property : Store ctx → Prop)
    (program : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (_commutes : SelectsRead read true program environment)
    (_preserved : ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      (∀ entry, 0 < (state.block entry).mass → property entry.1) →
      ∀ entry, 0 < ((program.execute environment Reference state).block entry).mass →
        property entry.1)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass → read entry.1 = true → property entry.1),
    ∀ entry, 0 < ((program.execute environment Reference state).block entry).mass →
      read entry.1 = true → property entry.1

private lemma selects_read_preserves_implication : SelectsReadPreservesImplicationStatement := by
  intro ctx services read property program environment commutes preserved
    Reference History finite state supported
  have selectedInput : ∀ entry,
      0 < ((state.selectClassical (fun entry => read entry.1) true).block entry).mass →
      property entry.1 := by
    intro entry positive
    have flag : read entry.1 = true :=
      ExecutionState.selectClassical_read_eq_of_block_ne_zero state
        (fun entry => read entry.1) true entry (by
          intro zero
          rw [zero, DensityOperator.zero_mass] at positive
          exact (lt_irrefl 0) positive)
    have prior : 0 < (state.block entry).mass := by
      simpa only [ExecutionState.selectClassical_block, flag, ite_true] using positive
    exact supported entry prior flag
  have selectedOutput := preserved (state.selectClassical (fun entry => read entry.1) true)
    selectedInput
  intro entry positive flag
  apply selectedOutput entry
  rw [commutes state]
  simpa only [ExecutionState.selectClassical_block, flag, ite_true] using positive

namespace Inputs

private lemma preparation_scalar_property {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx) (sampler : Parameters ctx)
    (selected : CStorageRef ctx (.unsignedWord 260))
    (property : CShape.Value (.unsignedWord 260) → Prop)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (supported : ∀ entry, 0 < (state.block entry).mass →
      property (entry.1.read (.storage selected))) :
    ∀ entry, 0 < (((original.preparation sampler).execute
      environment Reference state).block entry).mass →
      property (entry.1.read (.storage selected)) := by
  classical
  have chosen : SelectsRead (originalStorageRead selected
      (fun value => decide (property value))) true
      (original.preparation sampler) environment :=
    preparation_selects_storage (ctx := ctx) (services := services) original sampler selected
    (fun value => decide (property value)) true
    (by intro cardinality impossible; cases impossible) environment
    (fun index => middle_scalar_read sampler index selected environment)
  have preserved := selects_read_preserves_positive
    (originalStorageRead selected (fun value => decide (property value))) true
    (original.preparation sampler) environment chosen state
    (fun entry positive => decide_eq_true (supported entry positive))
  intro entry positive
  exact of_decide_eq_true (preserved entry positive)

private def latchSound {ctx : RuntimeCtx .quantum} {curve : CurveSpec 256}
    (accepted : CInputRef ctx .bit) (selected : CInputRef ctx (.unsignedWord 260))
    (basePoint targetPoint : Pure.Point curve) (store : Store ctx) : Prop :=
  (store.read accepted).toBool = true → (store.read selected).toNat • basePoint = targetPoint

private def checkerSoundInputs {ctx : RuntimeCtx .quantum}
    (original : Inputs ctx) (checkers : Checkers ctx)
    (basePoint targetPoint : Pure.Point original.curve) (store : Store ctx) : Prop :=
  PointRepresents original.curve (store.read original.base) basePoint ∧
  PointRepresents original.curve (store.read original.target) targetPoint ∧
  latchSound (.storage checkers.accepted.toCStorageRef) (.storage checkers.selected.toCStorageRef)
    basePoint targetPoint store

private def CheckerSoundnessStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs ctx) (sampler : Parameters ctx)
    (checkers : Checkers ctx) (basePoint targetPoint : Pure.Point original.curve)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (_distinct : checkers.keys.Nodup)
    (_baseFree : ∀ key ∈ checkers.keys, key ∉ original.base.storageKeys)
    (_targetFree : ∀ key ∈ checkers.keys, key ∉ original.target.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (_supported : ∀ entry, 0 < (state.block entry).mass →
      checkerSoundInputs original checkers basePoint targetPoint entry.1),
    ∀ entry, 0 < ((((original.checkerTail sampler checkers).code (services := services)).execute
      environment Reference state).block entry).mass →
      latchSound (.storage checkers.accepted.toCStorageRef)
        (.storage checkers.selected.toCStorageRef) basePoint targetPoint entry.1

private lemma checker_soundness : CheckerSoundnessStatement := by
  intro ctx services original sampler checkers basePoint targetPoint environment
    distinct baseFree targetFree Reference History finite state supported
  obtain ⟨record, actual, returned⟩ := original.checker_actualRecord sampler checkers environment
  rw [actual]
  apply Conditional.mapped_supported
  · exact supported
  · intro entry prior
    change (((record (entry.1, entry.2.1)).1.1.read
      (.storage checkers.accepted.toCStorageRef)).toBool = true →
        ((record (entry.1, entry.2.1)).1.1.read
          (.storage checkers.selected.toCStorageRef)).toNat • basePoint = targetPoint)
    rw [returned]
    exact original.checkerStore_preserves_soundness sampler checkers environment
      (entry.1, entry.2.1) basePoint targetPoint prior.1 prior.2.1
      distinct baseFree targetFree prior.2.2

private def CurrentPreparationSoundnessStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History))
    (_sound : ∀ entry, 0 < (state.block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1),
    ∀ entry, 0 < ((((original.currentInput lift same).preparation
      (original.currentSampler lift same scratch fresh)).execute
        environment Reference state).block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1

private lemma current_preparation_soundness : CurrentPreparationSoundnessStatement := by
  intro outer inner services original lift same scratch fresh environment basePoint targetPoint
    Reference History finite state sound
  have chosen : SelectsRead (fun store => (store.read (currentAccepted lift)).toBool) true
      ((original.currentInput lift same).preparation
        (original.currentSampler lift same scratch fresh)) environment :=
    original.retainedInput.fresh_preparation_selects_bit lift same scratch fresh environment
      (Checkers.retained outer).accepted.toCStorageRef true
  apply selects_read_preserves_implication
    (fun store => (store.read (currentAccepted lift)).toBool)
    (fun store => (store.read (.storage (currentCheckers lift).selected.toCStorageRef)).toNat •
      basePoint = targetPoint)
    ((original.currentInput lift same).preparation
      (original.currentSampler lift same scratch fresh)) environment chosen ?_ state sound
  intro currentReference currentHistory currentFinite current prior
  exact preparation_scalar_property (ctx := inner) (services := services)
    (original.currentInput lift same) (original.currentSampler lift same scratch fresh)
    (currentCheckers lift).selected.toCStorageRef
    (fun value => value.toNat • basePoint = targetPoint) environment current prior

private def FreshAttemptSoundnessStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve)
    (_prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History))
    (_supported : original.CurrentSupport lift basePoint targetPoint state)
    (_sound : ∀ entry, 0 < (state.block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1),
    ∀ entry, 0 < ((((original.currentInput lift same).attempt
      (original.currentSampler lift same scratch fresh) (currentCheckers lift)).execute
        environment Reference state).block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1

private lemma fresh_attempt_soundness : FreshAttemptSoundnessStatement := by
  intro outer inner services original lift same scratch fresh environment basePoint targetPoint
    prepared Reference History finite state supported sound
  rw [(original.currentInput lift same).attempt_code_eq
    (original.currentSampler lift same scratch fresh) (currentCheckers lift)]
  apply Circuit.supported_store_seq environment
    ((original.currentInput lift same).preparation (original.currentSampler lift same scratch
      fresh))
    (((original.currentInput lift same).checkerTail
      (original.currentSampler lift same scratch fresh) (currentCheckers lift)).code
        (services := services)) Reference state
    (latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
      basePoint targetPoint)
  have separated := original.transported_checker_separation lift same
  apply checker_soundness (ctx := inner) (services := services)
    (original.currentInput lift same) (original.currentSampler lift same scratch fresh)
    (currentCheckers lift) basePoint targetPoint environment
    separated.1 separated.2.1 separated.2.2
    (((original.currentInput lift same).preparation
      (original.currentSampler lift same scratch fresh)).execute environment Reference state)
  have preservedLatch := current_preparation_soundness (outer := outer)
    (inner := inner) (services := services) original lift same scratch fresh environment
    basePoint targetPoint state sound
  intro entry positive
  have facts := (prepared state supported) entry positive
  have points : PointRepresents (original.currentInput lift same).curve
      (entry.1.read (original.currentInput lift same).base) basePoint ∧
      PointRepresents (original.currentInput lift same).curve
        (entry.1.read (original.currentInput lift same).target) targetPoint := by
    simpa only [currentInput, retainedInput, transport, Transport.liftInput_compose]
      using facts.1
  exact ⟨points.1, points.2, preservedLatch entry positive⟩

private def FreshLoopSoundnessStatement : Prop :=
  ∀ {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport (persistentCtx outer 256 260) inner)
    (same : (persistentCtx outer 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Frame inner 256 256) (fresh : CallerFree scratch lift)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (basePoint targetPoint : Pure.Point original.curve) (count : Nat)
    (_prepared : original.PreparedSupport lift same scratch fresh environment basePoint targetPoint)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History))
    (_supported : original.CurrentSupport lift basePoint targetPoint state)
    (_sound : ∀ entry, 0 < (state.block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1),
    ∀ entry, 0 < (((Circuit.forRange count fun _ =>
      (original.currentInput lift same).attempt (services := services)
        (original.currentSampler lift same scratch fresh) (currentCheckers lift)).execute
          environment Reference state).block entry).mass →
      latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
        basePoint targetPoint entry.1

/-- Every actual retry preserves the sound original first-success latch with full input support. -/
lemma fresh_loop_soundness : FreshLoopSoundnessStatement := by
  intro outer inner services original lift same scratch fresh environment basePoint targetPoint
      count
    prepared Reference History finite state supported sound
  let invariant : Store inner → Prop := fun store =>
    Conditional.readConditions original basePoint targetPoint
      (fun {_} input => store.read (((Recovery.persistentTransport outer).compose lift).liftInput
        input)) ∧
    latchSound (currentAccepted lift) (.storage (currentCheckers lift).selected.toCStorageRef)
      basePoint targetPoint store
  have loop := preservesStore_forRange (environment := environment) count
    (fun _ => (original.currentInput lift same).attempt (services := services)
      (original.currentSampler lift same scratch fresh) (currentCheckers lift)) invariant
    (by
      intro index currentReference currentHistory currentFinite current prior
      have currentSupport : original.CurrentSupport lift basePoint targetPoint current :=
        fun entry positive => (prior entry positive).1
      have nextSupport := original.fresh_attempt_supported lift same scratch fresh environment
        basePoint targetPoint prepared current currentSupport
      have nextSound := fresh_attempt_soundness (outer := outer) (inner := inner)
        (services := services) original lift same scratch fresh environment basePoint targetPoint
        prepared current currentSupport (fun entry positive => (prior entry positive).2)
      exact fun entry positive => ⟨nextSupport entry positive, nextSound entry positive⟩)
    state (fun entry positive => ⟨supported entry positive, sound entry positive⟩)
  exact fun entry positive => (loop entry positive).2

end Inputs
end
end Storage
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
