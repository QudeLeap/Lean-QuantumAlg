/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.State.Requirement.Embedding
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.State.Promise.Reindex
import all QuantumAlg.Core.Execution.Context.Embedding.Selection.Marginal
import all QuantumAlg.Core.Execution.Input.Oracle.Embedding.Caller
import all QuantumAlg.Core.Execution.Input.Oracle.Projection
import all QuantumAlg.Core.Execution.State.Marginal.Reference
import all QuantumAlg.Core.Execution.Classical.Pushforward

/-!
# Complete transport of independently specified state promises

Actual output blocks are grouped by the placed classical read and projected
onto the original physical subsystem. Pure and mixed promises retain their
block mass, while joint promises retain the original external reference and
receive its original projected input. No additional purity, independence or
admission condition is imposed.
-/

namespace QuantumAlg.StateRequirement

noncomputable section

open Execution

attribute [local instance] Classical.decEq

variable {kind : ProblemKind} {localCtx caller : RuntimeCtx kind}
  (placement : ContextEmbedding localCtx caller) {Reference : Register}

private def projectedFinal
    (final : ExecutionState (Store caller) (caller.register.prod Reference)) :
    ExecutionState (Store localCtx) (localCtx.register.prod Reference) :=
  ((final.mapClassical (fun store => (placement.store store).1)).reindex
    (S := localCtx.register.prod (placement.frame.register.prod Reference))
    (placement.referenceBasis Reference)).forgetReferenceFrame

private lemma projected_read {shape : CShape} (read : OutputRead localCtx shape)
    (final : ExecutionState (Store caller) (caller.register.prod Reference)) :
    (projectedFinal placement final).mapClassical read.eval =
      ((final.mapClassical (placement.outputRead read).eval).reindex
        (S := localCtx.register.prod (placement.frame.register.prod Reference))
        (placement.referenceBasis Reference)).forgetReferenceFrame := by
  rw [projectedFinal, ← ExecutionState.forgetReferenceFrame_mapClassical,
    ExecutionState.coordinate_reindex_mapClassical,
    ExecutionState.executionState_mapClassical_comp]
  apply congrArg (fun state : ExecutionState shape.Value (caller.register.prod Reference) =>
    (state.reindex (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame)
  apply ExecutionState.executionState_mapClassical_congr
  funext store
  symm
  simpa only [Prod.eta, Equiv.symm_apply_apply, Function.comp_apply] using
    placement.contextEmbedding_outputRead_eval (placement.store store).1
      (placement.store store).2 read

private lemma projected_joint {shape : CShape} (selection : Finset (Fin localCtx.systemCount))
    (read : OutputRead localCtx shape)
    (final : ExecutionState (Store caller) (caller.register.prod Reference)) (value : shape.Value) :
    (DensityOperator.observeSelectionWithReference caller.quantumLayout
      (placement.selection selection) Reference
      ((final.mapClassical (placement.outputRead read).eval).block value)).reindex
        (S := (localCtx.quantumLayout.selectedRegister selection).prod Reference)
        ((placement.selectedBasis selection).symm.prodCongr (Equiv.refl Reference.Index)) =
      DensityOperator.observeSelectionWithReference localCtx.quantumLayout selection Reference
        (((projectedFinal placement final).mapClassical read.eval).block value) := by
  rw [projected_read]
  exact placement.contextEmbedding_observeSelectionWithReference_project selection Reference _

private lemma projected_marginal {shape : CShape}
    (selection : Finset (Fin localCtx.systemCount)) (read : OutputRead localCtx shape)
    (final : ExecutionState (Store caller) (caller.register.prod Reference)) (value : shape.Value) :
    (DensityOperator.observeSelection caller.quantumLayout
      (placement.selection selection) Reference
      ((final.mapClassical (placement.outputRead read).eval).block value)).reindex
        (placement.selectedBasis selection).symm =
      DensityOperator.observeSelection localCtx.quantumLayout selection Reference
        (((projectedFinal placement final).mapClassical read.eval).block value) := by
  rw [projected_read]
  exact placement.contextEmbedding_observeSelection_project selection Reference _

private lemma promise_of_projected {R S : Register} (basis : R.Index ≃ S.Index)
    (promise : StatePromise R) (actual : DensityOperator S)
    (holds : promise.Holds (actual.reindex basis.symm)) :
    (promise.reindex basis).Holds actual := by
  have restored : (actual.reindex (S := R) basis.symm).reindex basis = actual := by
    rw [DensityOperator.reindex_trans]
    simpa only [Equiv.symm_trans_self] using DensityOperator.reindex_refl actual
  have transferred :=
    (StatePromise.statePromise_reindex_holds_iff basis promise
      (actual.reindex basis.symm)).mpr holds
  rwa [restored] at transferred

/-- An exact local final-state projection transports every original state promise. -/
lemma stateRequirement_embed_holds_of_projection
    {oracles : ClassicalOracleModel} (requirement : StateRequirement localCtx localCtx)
    (input : OracleInput oracles caller Reference)
    (final : ExecutionState (Store caller) (caller.register.prod Reference))
    (localFinal : ExecutionState (Store localCtx) (localCtx.register.prod Reference))
    (projected : ((final.mapClassical (fun store => (placement.store store).1)).reindex
      (S := localCtx.register.prod (placement.frame.register.prod Reference))
      (placement.referenceBasis Reference)).forgetReferenceFrame = localFinal)
    (holds : requirement.Holds (placement.localInput input).caller localFinal) :
    (requirement.embed placement).Holds input.caller final := by
  change projectedFinal placement final = localFinal at projected
  cases requirement with
  | marginal selection read target =>
      change ∀ value, (target (placement.localInput input).caller.localState value).Holds _
        at holds
      rw [placement.contextEmbedding_localInput_caller_localState,
        placement.contextEmbedding_framedInput_caller_localState] at holds
      intro value
      apply promise_of_projected
      rw [projected_marginal, projected]
      exact holds value
  | jointReference selection read target =>
      change ∀ value, (target Reference (placement.localInput input).caller value).Holds _
        at holds
      rw [placement.contextEmbedding_localInput_caller] at holds
      intro value
      apply promise_of_projected
      have observed := projected_joint placement selection read final value
      rw [projected] at observed
      exact observed.symm ▸ holds value

end

end QuantumAlg.StateRequirement
