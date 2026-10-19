/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Cycle.Admission
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Reference.Probability
import all QuantumAlg.Core.Execution.SelectionAll.Reference
import all QuantumAlg.Core.Execution.Classical.Support
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Util.PMF.FiniteWeights

/-!
# Complete batch state requirements from the independent source law

A completed batch returns its original factor distribution and leaves the
entire bank in the predetermined source seed, jointly with the complete incoming
reference. The actual output law and full mixed-state promise follow from the
same weighted reference identity. Zero-mass outputs require no division.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}

/-- The complete original source distribution acts on the actual full reference entries. -/
def ReferenceLaw (program : AlgorithmRun model pre post shape) {Reference : Register}
    (input : OracleInput model.classicalOracles pre Reference) (distribution : PMF shape.Value) :
    Prop :=
  ∀ (weight : shape.Value → ℂ) (leftRef rightRef : Reference.Index),
    ExecutionState.referenceFiberSum (program.execute environment Reference input.state)
      (fun entry _ => weight (program.result entry)) leftRef rightRef =
        ExecutionState.referenceFiberSum input.state
          (fun _ _ => ∑ value, ((distribution value).toReal : ℂ) * weight value)
          leftRef rightRef

/-- Full weighted reference observations determine the actual result distribution. -/
lemma outputDistribution_of_referenceLaw (program : AlgorithmRun model pre post shape)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference)
    (distribution : PMF shape.Value) (law : ReferenceLaw (environment := environment)
      program input distribution) :
    program.outputDistribution environment input = distribution := by
  apply ExecutionState.toPMF_map_eq_of_referenceFiberSum input.state
    (program.execute
      environment Reference input.state) input.normalized (program.execute_normalized environment
        input)
    program.result distribution
  intro selected leftRef rightRef
  exact (law (fun value => if value = selected then 1 else 0) leftRef rightRef).trans
    (congrArg (fun coefficient : ℂ => ExecutionState.referenceFiberSum input.state
      (fun _ _ => coefficient) leftRef rightRef)
      (PMF.sum_toReal_indicator distribution selected))

/-- Independent full-bank/reference target for each actual retained batch result. -/
def batchRequirement (seed : post.register.Index) (read : OutputRead post shape) :
    StateRequirement pre post :=
  .jointReference Finset.univ read fun Reference input _ =>
    .mixed (DensityOperator.observeSelectionWithReference post.quantumLayout
      Finset.univ Reference (BasisReference.target seed input.state.referenceMarginal))
      ((DensityOperator.observeSelectionWithReference_mass post.quantumLayout
        Finset.univ Reference _).trans
        ((BasisReference.target_mass seed input.state.referenceMarginal).trans
          ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized)))

/-- The same source law and actual final seed establish every full output-state block. -/
lemma batchRequirement_holds (program : AlgorithmRun model pre post shape)
    (seed : post.register.Index) (read : OutputRead post shape)
    (reads : program.output.eval = read.eval)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference)
    (distribution : PMF shape.Value) (law : ReferenceLaw (environment := environment)
      program input distribution)
    (seeded : BasisSeeded.Holds seed (program.execute environment Reference input.state)) :
    (batchRequirement seed read).Holds input.caller
      (program.finalState environment Reference input.state) := by
  intro selected
  let actual := ((program.execute
    environment Reference input.state).mapClassical program.result).block selected
  have normalized : input.caller.state.referenceMarginal.IsNormalized :=
    (ExecutionState.referenceMarginal_mass input.caller.state).trans input.caller.normalized
  have sameReference : input.state.referenceMarginal = input.caller.state.referenceMarginal := by
    unfold ExecutionState.referenceMarginal
    rw [OracleInput.oracleInput_caller_quantumMarginal]
  have entries (left right : post.register.Index) (leftRef rightRef : Reference.Index) :
      actual.matrix (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          ((distribution selected).toReal : ℂ) *
            input.caller.state.referenceMarginal.matrix leftRef rightRef else 0 := by
    have observed := BasisSeeded.readout_entry seed (program.execute
      environment Reference input.state)
      seeded program.output.eval selected left right leftRef rightRef
    have scalar := (law (fun value => if value = selected then 1 else 0)
      leftRef rightRef).trans
      ((congrArg (fun coefficient : ℂ => ExecutionState.referenceFiberSum input.state
        (fun _ _ => coefficient) leftRef rightRef)
        (PMF.sum_toReal_indicator distribution selected)).trans
          (ExecutionState.referenceFiberSum_constant_eq input.state _ leftRef rightRef))
    rw [sameReference] at scalar
    exact observed.trans (congrArg (fun coefficient : ℂ =>
      if left = seed ∧ right = seed then coefficient else 0) scalar)
  have joint := BasisReference.promise_of_entries seed input.caller.state.referenceMarginal
    normalized actual (distribution selected).toReal entries
  change (StatePromise.mixed
    (DensityOperator.observeSelectionWithReference post.quantumLayout Finset.univ Reference
      (BasisReference.target seed input.caller.state.referenceMarginal)) _).Holds
    (DensityOperator.observeSelectionWithReference post.quantumLayout Finset.univ Reference
      (((program.finalState environment Reference input.state).mapClassical read.eval).block
        selected))
  rw [← reads, AlgorithmRun.finalState_readout]
  exact StatePromise.mixed_fullSelection post.quantumLayout Reference
    (BasisReference.target seed input.caller.state.referenceMarginal)
    (BasisReference.target_normalized seed input.caller.state.referenceMarginal normalized)
    actual joint

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles
