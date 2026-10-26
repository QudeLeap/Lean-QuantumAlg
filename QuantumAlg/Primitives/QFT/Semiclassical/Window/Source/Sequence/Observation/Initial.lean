/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Observation.Reference
import all QuantumAlg.Core.Base.Gate.Effect.FixedInput

/-!
# Initial-source observations with the original record equality procedure

All source carriers remain symbolic. Definite classical records use one
explicit equality procedure throughout the complete state identity. The
actual code and source-stage list retain their original interpreters and
histories. A concrete consumer supplies the already proved preparation and
reference laws internally; no physical source system is prepared here.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- The same definite record and physical input, with its explicit original decision. -/
def initialPhysicalState {Record : Type} [Fintype Record] {R Reference : Register}
    (decision : DecidableEq Record) (original : Record) (physical : NormalizedVector R)
    (reference : NormalizedVector Reference) : ExecutionState Record (R.prod Reference) :=
  @ExecutionState.ofValue Record _ (R.prod Reference) decision original
    (DensityOperator.ofPure (NormalizedVector.prodTensor physical reference))

/-- Only a mathematical auxiliary ket is adjoined to the same complete original record. -/
def initialSourceState {Record : Type} [Fintype Record] {R S Reference : Register}
    (decision : DecidableEq Record) (original : Record) (physical : NormalizedVector R)
    (frame : S.Index) (reference : NormalizedVector Reference) :
    ExecutionState Record (R.prod (S.prod Reference)) :=
  initialPhysicalState decision original physical
    (NormalizedVector.prodTensor (NormalizedVector.ket frame) reference)

/-- Equality procedures describe the same definite classical record on the complete state. -/
lemma window_source_ofValue_decisions {Record : Type} [Fintype Record] {R : Register}
    (first second : DecidableEq Record) (original : Record) (state : DensityOperator R) :
    @ExecutionState.ofValue Record _ R first original state =
      @ExecutionState.ofValue Record _ R second original state :=
  congrArg (fun decision : DecidableEq Record =>
    @ExecutionState.ofValue Record _ R decision original state) (Subsingleton.elim first second)

/-- The auxiliary ket disappears with the same explicit decision on both original records. -/
lemma window_source_initial_forget {Record : Type} [Fintype Record]
    {R S Reference : Register} (decision : DecidableEq Record) (original : Record)
    (physical : NormalizedVector R) (frame : S.Index)
    (reference : NormalizedVector Reference) :
    ExecutionState.forgetReferenceFrame (R := R) (S := S) (T := Reference)
        (initialSourceState decision original physical frame reference) =
      initialPhysicalState decision original physical reference := by
  rw [Subsingleton.elim decision (Classical.decEq Record)]
  exact window_source_forget_ket_frame original physical frame reference

/-- Preparation changes only the auxiliary vector, retaining the actual classical record. -/
lemma window_source_initial_prepare {Record : Type} [Fintype Record]
    {R S Reference : Register} (decision : DecidableEq Record) (original : Record)
    (physical : NormalizedVector R) (frame : S.Index)
    (reference : NormalizedVector Reference) (operator : UnitaryOperator S) :
    (initialSourceState decision original physical frame reference).applyUnitary
        (fun _ => UnitaryOperator.prodTensor (1 : UnitaryOperator R)
          (UnitaryOperator.prodTensor operator (1 : UnitaryOperator Reference))) =
      initialPhysicalState decision original physical
        (NormalizedVector.prodTensor (operator.apply (NormalizedVector.ket frame)) reference) := by
  rw [Subsingleton.elim decision (Classical.decEq Record)]
  exact window_source_prepare_pure_record original physical (NormalizedVector.ket frame)
    reference operator

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference S : Register}

/-- The literal Store observer equals its same initial-basis compressed effect. -/
lemma window_source_initial_basisSlice_storeWeight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (source : NormalizedVector Reference)
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    (Effect.basisSliceEffect
      (Stage.observation environment stages (fun record => effects record.1) original)
      label).weight (DensityOperator.ofPure source) =
      Stage.storeWeight environment stages
        (initialPhysicalState decision original (NormalizedVector.ket label) source) effects := by
  let observed := Stage.observation environment stages (History := History)
    (fun record => effects record.1)
  let input := NormalizedVector.prodTensor (NormalizedVector.ket label) source
  calc
    _ = (observed original).weight (DensityOperator.ofPure input) :=
      Effect.basisSliceEffect_weight_of_pure (observed original) label source input
        (fun _ _ => NormalizedVector.prodTensor_apply _ _ _)
    _ = (initialPhysicalState decision original (NormalizedVector.ket label)
        source).effectWeight observed :=
      (ExecutionState.effectWeight_ofValue_decision decision original
        (DensityOperator.ofPure input) observed).symm
    _ = _ := (Stage.window_sourceSequence_storeWeight environment stages
      (initialPhysicalState decision original (NormalizedVector.ket label) source) effects).symm

/-- Exact actual initial event from proved reference and source-preparation identities. -/
lemma window_source_initial_event
    (code : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true)
    (stages : List (Stage ctx operations services (S.prod Reference)))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {History : Type} [Fintype History]
    (decision : DecidableEq (Store ctx × (services.HiddenState × History)))
    (original : Store ctx × (services.HiddenState × History)) (label : ctx.register.Index)
    (frame : S.Index) (reference : NormalizedVector Reference) (operator : UnitaryOperator S)
    (event : Store ctx → Bool)
    (natural : code.execute environment Reference
        (ExecutionState.forgetReferenceFrame (R := ctx.register) (S := S) (T := Reference)
          (initialSourceState decision original (NormalizedVector.ket label) frame reference)) =
      (code.execute environment (S.prod Reference)
        (initialSourceState decision original (NormalizedVector.ket label)
          frame reference)).forgetReferenceFrame)
    (prepared : Execution.storeEffectWeight code environment
        (initialSourceState decision original (NormalizedVector.ket label) frame reference)
        (Execution.recordEventEffect (ctx.register.prod (S.prod Reference)) event) =
      Stage.storeWeight environment stages
        ((initialSourceState decision original (NormalizedVector.ket label)
          frame reference).applyUnitary (fun _ => sourcePreparationAction Reference operator))
        (Execution.recordEventEffect (ctx.register.prod (S.prod Reference)) event)) :
    Execution.storeEffectWeight code environment
        (initialPhysicalState decision original (NormalizedVector.ket label) reference)
        (Execution.recordEventEffect (ctx.register.prod Reference) event) =
      (Effect.basisSliceEffect
        (Stage.observation environment stages (fun record => Execution.recordEventEffect
          (ctx.register.prod (S.prod Reference)) event record.1) original) label).weight
        (DensityOperator.ofPure (NormalizedVector.prodTensor
          (operator.apply (NormalizedVector.ket frame)) reference)) := by
  let initial := initialSourceState decision original (NormalizedVector.ket label) frame reference
  have unprepared := window_source_actualStoreEvent_forget code environment initial event natural
  have forgotten := window_source_initial_forget decision original
    (NormalizedVector.ket label) frame reference
  have originalInput :=
    (congrArg (fun current : State ctx Reference (services.HiddenState × History) =>
      Execution.storeEffectWeight code environment current
        (Execution.recordEventEffect (ctx.register.prod Reference) event)) forgotten).symm.trans
          unprepared
  have changed := window_source_initial_prepare decision original
    (NormalizedVector.ket label) frame reference operator
  have preparation := prepared.trans
    (congrArg (fun current : State ctx (S.prod Reference) (services.HiddenState × History) =>
      Stage.storeWeight environment stages current
        (Execution.recordEventEffect (ctx.register.prod (S.prod Reference)) event)) changed)
  have observed := window_source_initial_basisSlice_storeWeight environment stages decision
    original label (NormalizedVector.prodTensor (operator.apply (NormalizedVector.ket frame))
      reference) (Execution.recordEventEffect (ctx.register.prod (S.prod Reference)) event)
  exact originalInput.trans (preparation.trans observed.symm)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
