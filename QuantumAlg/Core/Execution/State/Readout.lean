/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Core.Execution.Input.Oracle
import all QuantumAlg.Core.Execution.MarginalLaws
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Full joint state promises at an actual algorithm readout

The generic bridge forgets only mathematical execution labels. It transports
the exact full register-reference block, including impossible output blocks,
to the stored readout of the same run. Concrete programs need not unfold their
complete path types while proving this transport.
-/

namespace QuantumAlg

noncomputable section

namespace ExecutionState

/-- Reindexing classical labels preserves the entire external-reference marginal. -/
lemma mapClassical_referenceMarginal {C D : Type} [Fintype C] [Fintype D] [DecidableEq D]
    {R Reference : Register} (state : ExecutionState C (Register.prod R Reference))
    (read : C → D) : (state.mapClassical read).referenceMarginal = state.referenceMarginal :=
  congrArg (fun density : DensityOperator (Register.prod R Reference) =>
    DensityOperator.marginalLeft (density.reindex
      (S := Register.prod Reference R) (Equiv.prodComm R.Index Reference.Index)))
    (mapClassical_quantumMarginal state read)

end ExecutionState

namespace Execution.BasisSeeded

/-- A fixed physical seed and the full weighted reference law determine every output block. -/
lemma readout_entry_of_reference {kind : ProblemKind}
    {source ctx : RuntimeCtx kind} {Reference : Register}
    {SourceHistory History Outcome : Type}
    [Fintype SourceHistory] [Fintype History] [Fintype Outcome] [DecidableEq Outcome]
    (original : State source Reference SourceHistory) (state : State ctx Reference History)
    (seed : ctx.register.Index) (seeded : Holds seed state)
    (read : Store ctx → Outcome) (distribution : PMF Outcome)
    (reference : ∀ (weight : Outcome → ℂ) (leftRef rightRef : Reference.Index),
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (read entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum original
        (fun _ _ => ∑ selected : Outcome,
          ((distribution selected).toReal : ℂ) * weight selected) leftRef rightRef)
    (value : Outcome) (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    ((state.mapClassical (fun entry => read entry.1)).block value).matrix
        (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then
        ((distribution value).toReal : ℂ) * original.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  have observed := readout_entry (ctx := ctx) (Reference := Reference) (History := History)
    seed state seeded read value left right leftRef rightRef
  have actual := reference (fun selected => if selected = value then 1 else 0) leftRef rightRef
  have scalar := actual.trans
    ((congrArg (fun coefficient : ℂ =>
      ExecutionState.referenceFiberSum original (fun _ _ => coefficient) leftRef rightRef)
      (PMF.sum_toReal_indicator distribution value)).trans
      (ExecutionState.referenceFiberSum_constant_eq original _ leftRef rightRef))
  exact observed.trans (congrArg (fun coefficient : ℂ =>
    if left = seed ∧ right = seed then coefficient else 0) scalar)

end Execution.BasisSeeded

namespace AlgorithmRun

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- An exact basis-reference entry law gives the full actual stored-output mixed promise. -/
lemma basisReference_readout_of_entries {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape) (environment : model.Environment)
    {Reference : Register}
    (original : OracleInput model.classicalOracles pre Reference)
    (seed : post.register.Index) (value : shape.Value) (probability : ℝ)
    (entries : ∀ left right leftRef rightRef,
      (((program.execute environment Reference original.state).mapClassical
        program.result).block value).matrix
          (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          (probability : ℂ) * original.state.referenceMarginal.matrix leftRef rightRef else 0) :
    (StatePromise.mixed
      (BasisReference.target (R := post.register) seed original.caller.state.referenceMarginal)
      (BasisReference.target_normalized (R := post.register) seed
        original.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass original.caller.state).trans
          original.caller.normalized))).Holds
      (((program.finalState environment Reference original.state).mapClassical
        program.output.eval).block
        value) := by
  have sameReference : original.caller.state.referenceMarginal =
      original.state.referenceMarginal := by
    unfold ExecutionState.referenceMarginal
    rw [OracleInput.oracleInput_caller_quantumMarginal]
  have actual := BasisReference.promise_of_entries (R := post.register) seed
    original.caller.state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass original.caller.state).trans
      original.caller.normalized)
    (((program.execute environment Reference original.state).mapClassical
      program.result).block value)
    probability (by simpa only [sameReference] using entries)
  have readout := congrArg (fun final => final.block value)
    (finalState_readout program environment Reference original.state)
  exact readout.symm ▸ actual

/-- A history-polymorphic circuit entry law transports to its complete actual run readout. -/
lemma basisReference_readout_of_executionEntries {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape) (environment : model.Environment)
    (seed : post.register.Index)
    (distribution : PMF shape.Value)
    (entries : ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History)),
      state.IsNormalized → ∀ value left right leftRef rightRef,
      (((program.code.execute environment Reference state).mapClassical
          (fun entry => program.output.eval entry.1)).block value).matrix
          (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          ((distribution value).toReal : ℂ) * state.referenceMarginal.matrix leftRef rightRef
        else 0)
    {Reference : Register} (original : OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    (StatePromise.mixed
      (BasisReference.target (R := post.register) seed original.caller.state.referenceMarginal)
      (BasisReference.target_normalized (R := post.register) seed
        original.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass original.caller.state).trans
          original.caller.normalized))).Holds
      (((program.finalState environment Reference original.state).mapClassical
        program.output.eval).block
        value) := by
  let entered : State pre Reference (model.HiddenState × Store pre) :=
    original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))
  have normalized := original.state.mapClassical_normalized original.normalized
    (fun entry => (entry.1, (entry.2, entry.1)))
  apply basisReference_readout_of_entries program environment original seed value
    (distribution value).toReal
  intro left right leftRef rightRef
  have actual := entries entered normalized value left right leftRef rightRef
  exact actual.trans (congrArg (fun reference : DensityOperator Reference =>
    if left = seed ∧ right = seed then
      ((distribution value).toReal : ℂ) * reference.matrix leftRef rightRef else 0)
    (ExecutionState.mapClassical_referenceMarginal original.state
      (fun entry => (entry.1, (entry.2, entry.1)))))

end AlgorithmRun

end

end QuantumAlg
