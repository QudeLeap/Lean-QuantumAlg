/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/
module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Soundness

/-! # Lexical feedback transport for the original supported sound latch -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
namespace Storage

open Execution ClassicalWorkspace ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

noncomputable section
local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private def SoundBound {outer inner : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve)
    (accepted : CInputRef inner .bit) (selected : CInputRef inner (.unsignedWord 260))
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) : Prop :=
  ∀ {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (services.HiddenState × History)),
    Conditional.inputsSupported original lift basePoint targetPoint state →
    (∀ entry, 0 < (state.block entry).mass →
      Inputs.latchSound accepted selected basePoint targetPoint entry.1) →
    ∀ entry, 0 < ((code.execute environment Reference state).block entry).mass →
      Inputs.latchSound accepted selected basePoint targetPoint entry.1

private lemma workspace_sound {outer inner : RuntimeCtx .quantum}
    {services : ClassicalOracleModel} (original : Inputs outer) (lift : Transport outer inner)
    (basePoint targetPoint : Pure.Point original.curve)
    (accepted : CInputRef inner .bit) (selected : CInputRef inner (.unsignedWord 260))
    (key : StorageKey) (shape : CShape) (fresh : key ∉ inner.keys)
    (body : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services)
      (inner.addWorkspace key shape fresh) (inner.addWorkspace key shape fresh))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (bodySound : SoundBound original (lift.underWorkspace key shape fresh) basePoint targetPoint
      (accepted.underWorkspace key shape fresh) (selected.underWorkspace key shape fresh)
      body environment) :
    SoundBound original lift basePoint targetPoint accepted selected
      (Circuit.workspace (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        inner key shape fresh body) environment := by
  intro Reference History finite state supported sound
  have allocated : ∀ entry, 0 < ((state.pushWorkspace key shape fresh).block entry).mass →
      Inputs.latchSound (accepted.underWorkspace key shape fresh)
        (selected.underWorkspace key shape fresh) basePoint targetPoint entry.1 := by
    rw [State.state_pushWorkspace_as_mapClassical]
    apply Conditional.mapped_supported
    · exact sound
    · intro entry prior
      simpa only [Inputs.latchSound, Store.read_pushWorkspace_underWorkspace] using prior
  have returned := bodySound (state.pushWorkspace key shape fresh)
    (Conditional.inputsSupported_push original lift basePoint targetPoint state
      key shape fresh supported) allocated
  rw [Circuit.execute_workspace]
  unfold State.popWorkspace
  apply Conditional.mapped_supported
  · exact returned
  · intro entry prior
    simpa only [Inputs.latchSound, Store.read_popWorkspace_underWorkspace] using prior

private lemma withFrame_sound {outer ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs outer) (initialLift : Transport outer ctx)
    (basePoint targetPoint : Pure.Point original.curve)
    (accepted : CInputRef ctx .bit) (selected : CInputRef ctx (.unsignedWord 260))
    (wordWidth parityCount : Nat)
    (body : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner),
      ctx.quantumLayout.wires = inner.quantumLayout.wires →
      (scratch : Frame inner wordWidth parityCount) → CallerFree scratch lift →
      Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) inner inner)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    (bodySound : ∀ {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
      (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)
      (scratch : Frame inner wordWidth parityCount) (fresh : CallerFree scratch lift),
      SoundBound original (initialLift.compose lift) basePoint targetPoint
        (lift.liftInput accepted) (lift.liftInput selected) (body lift same scratch fresh)
        environment) :
    SoundBound original initialLift basePoint targetPoint accepted selected
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := by
  have actual : SoundBound original (initialLift.compose (Transport.id ctx))
      basePoint targetPoint ((Transport.id ctx).liftInput accepted)
      ((Transport.id ctx).liftInput selected)
      (withFrame (model := .quantum AlgorithmGate.model .empty BitWord.model services)
        ctx wordWidth parityCount body) environment := withCellsWithQuantumWiresFrom_property
    (model := .quantum AlgorithmGate.model .empty BitWord.model services) (Transport.id ctx) rfl
    (shapes wordWidth parityCount)
    (fun cells distinct lift separated same =>
      body lift (quantumLayout_wires_of_quantumWires same) (Frame.ofCells cells distinct)
        (ofCells_callerFree cells distinct lift separated))
    (fun lift _ code => SoundBound original (initialLift.compose lift) basePoint targetPoint
      (lift.liftInput accepted) (lift.liftInput selected) code environment)
    (by
      intro inner lift same key shape fresh code established
      apply workspace_sound original (initialLift.compose lift) basePoint targetPoint
        (lift.liftInput accepted) (lift.liftInput selected) key shape fresh code environment
      intro Reference History finite state supported
      have currentSupport : Conditional.inputsSupported original
          (initialLift.compose (lift.underWorkspace key shape fresh))
          basePoint targetPoint state := by
        simpa only [Conditional.compose_underWorkspace] using supported
      have returned := @established Reference History finite state currentSupport
      simpa only [Transport.liftInput_underWorkspace] using returned)
    (by
      intro inner cells distinct lift separated same Reference History finite state supported sound
      exact @bodySound inner lift (quantumLayout_wires_of_quantumWires same)
        (Frame.ofCells cells distinct) (ofCells_callerFree cells distinct lift separated)
        Reference History finite state supported sound)
  intro Reference History finite state supported
  have currentSupport : Conditional.inputsSupported original
      (initialLift.compose (Transport.id ctx)) basePoint targetPoint state := by
    simpa only [Conditional.compose_id] using supported
  have returned := @actual Reference History finite state currentSupport
  simpa only [Transport.liftInput_id] using returned

end
end Storage
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
