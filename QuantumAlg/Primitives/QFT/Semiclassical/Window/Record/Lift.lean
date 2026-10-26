/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Execution
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Record.Inverse
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Composition.Resources
import all QuantumAlg.Core.Execution.Time

/-!
# The same actual window inside a caller that permits classical workspaces

Identity embedding retains the original complete Store, actual Path and
arbitrary reference, and introduces no physical movement or native event.
The measured Fourier child remains allocation-free. Its caller may therefore
compose a real table-building workspace between windows without relabelling
that allocating wrapper as an allocation-free program.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {allowAllocation : Bool}

private lemma conditional_values {Value : Type} {proposition : Prop}
    (first second : Decidable proposition) (yes no : Value) :
    @ite Value proposition first yes no = @ite Value proposition second yes no := by
  cases first with
  | isTrue chosen =>
      cases second with
      | isTrue _ => rfl
      | isFalse absent => exact False.elim (absent chosen)
  | isFalse absent =>
      cases second with
      | isTrue chosen => exact False.elim (absent chosen)
      | isFalse _ => rfl

/-- A literal identity placement changes only the caller's permitted allocation index. -/
def liftedInverse (ports : Ports ctx totalBits active) :
    Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx allowAllocation :=
  .embed (ContextEmbedding.identity ctx)
    (inverseCode (operations := operations) (services := services) ports)

/-- Exact full-state execution of the same measured child, including all stored history fibers. -/
lemma window_liftedInverse_execute (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (liftedInverse (allowAllocation := allowAllocation) ports).execute
      environment Reference state = (inverseCode ports).execute environment Reference state :=
  Circuit.execute_identity_embed (inverseCode ports) environment Reference state

/-- The original full-record source rows hold at the caller's actual allocation index. -/
lemma window_liftedInverse_source_record_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × (History ×
      (liftedInverse (operations := operations) (services := services)
        (allowAllocation := allowAllocation) ports).Path))) :
    (((liftedInverse (allowAllocation := allowAllocation) ports).execute
      environment Reference state).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History), ∑ outcome : Bits active,
        if Execution.Instrument.retainedRecord
            (inverseStoreRecord (operations := operations) (services := services) ports)
              original outcome = result then
          sourceWindowKraus ports Reference original.1 outcome * (state.block original).matrix *
            (sourceWindowKraus ports Reference original.1 outcome).conjTranspose
        else 0 := by
  refine (congrArg (fun executed : State ctx Reference (services.HiddenState ×
      (History × (inverseCode (operations := operations) (services := services) ports).Path)) =>
        (executed.block result).matrix)
    (window_liftedInverse_execute (allowAllocation := allowAllocation)
      ports environment Reference state)).trans ?_
  refine (window_inverseCode_source_record_matrix ports environment Reference state result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  exact conditional_values _ _ _ _

lemma window_liftedInverse_eventTrace (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).eventTrace path =
      (inverseCode (operations := operations) (services := services) ports).eventTrace path := rfl

lemma window_liftedInverse_quantumTime (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).quantumTime path =
      (inverseCode (operations := operations) (services := services) ports).quantumTime path :=
  Circuit.quantumTime_embed
    (model := .quantum AlgorithmGate.model .empty operations services)
    (localCtx := ctx) (caller := ctx) (allowAllocation := allowAllocation)
    (ContextEmbedding.identity ctx)
    (inverseCode (operations := operations) (services := services) ports) path

lemma window_liftedInverse_peakResidentSpace (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).peakResidentSpace path =
      ctx.residentSpace :=
  Circuit.peakResidentSpace_embed
    (model := .quantum AlgorithmGate.model .empty operations services)
    (localCtx := ctx) (caller := ctx) (allowAllocation := allowAllocation)
    (ContextEmbedding.identity ctx)
    (inverseCode (operations := operations) (services := services) ports) path

lemma window_liftedInverse_peakAuxiliarySpace (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (liftedInverse (operations := operations) (services := services)
      (allowAllocation := allowAllocation) ports).peakAuxiliarySpace path =
      ctx.auxiliarySpace :=
  Circuit.peakAuxiliarySpace_embed
    (model := .quantum AlgorithmGate.model .empty operations services)
    (localCtx := ctx) (caller := ctx) (allowAllocation := allowAllocation)
    (ContextEmbedding.identity ctx)
    (inverseCode (operations := operations) (services := services) ports) path

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
