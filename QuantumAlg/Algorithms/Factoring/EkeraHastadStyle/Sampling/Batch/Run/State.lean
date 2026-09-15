/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Output.State
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Run.Probability
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Classical.Support

/-!
# Complete actual run blocks with the restored bank and incoming reference

Forgetting the mathematical path records leaves the same actual output
blocks. Each such block has the reloaded bank seed tensor the original
reference density, weighted by the original source probability. The proof
retains both reference coordinates and admits arbitrary correlated incoming
classical storage. Borrowed storage restoration is proved separately.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem run_output_entry {kind : ProblemKind} {pre post : RuntimeCtx kind}
    {shape : CShape} (program : AlgorithmRun pre post shape) (seed : post.register.Index)
    (coefficient : shape.Value → ℂ)
    (executeEntry : ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State pre Reference History) (selected : shape.Value)
      (left right : post.register.Index) (leftRef rightRef : Reference.Index),
      (((program.code.execute Reference state).mapClassical
        (fun entry => program.output.eval entry.1)).block selected).matrix
          (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          ExecutionState.referenceFiberSum state
            (fun _ _ => coefficient selected) leftRef rightRef else 0)
    {Reference : Register}
    (initial : ExecutionState (Store pre) (Register.prod pre.register Reference))
    (selected : shape.Value) (left right : post.register.Index)
    (leftRef rightRef : Reference.Index) :
    (((program.finalState Reference initial).mapClassical
      program.output.eval).block selected).matrix
        (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then
        coefficient selected * initial.referenceMarginal.matrix leftRef rightRef else 0 := by
  let entered : State pre Reference (Store pre) :=
    initial.mapClassical (fun store => (store, store))
  have entryEquation : program.execute Reference initial =
      program.code.execute Reference entered := by
    unfold AlgorithmRun.execute
    apply congrArg (fun state : State pre Reference (Store pre) =>
      program.code.execute Reference state)
    congr 1
  have runEquation := AlgorithmRun.finalState_readout program Reference initial
  have executionEquation := congrArg
    (fun state : ExecutionState program.Record (Register.prod post.register Reference) =>
      state.mapClassical (fun record => program.output.eval record.1)) entryEquation
  have readoutEquation := congrArg
    (fun state : ExecutionState shape.Value (Register.prod post.register Reference) =>
      (state.block selected).matrix (left, leftRef) (right, rightRef))
    (runEquation.trans executionEquation)
  refine readoutEquation.trans
    ((executeEntry entered selected left right leftRef rightRef).trans ?_)
  exact congrArg
    (fun scalar : ℂ => if left = seed ∧ right = seed then scalar else 0)
    ((ExecutionState.referenceFiberSum_mapClassical initial
      (fun store => (store, store)) (fun _ _ => coefficient selected)
      leftRef rightRef).trans
        (ExecutionState.referenceFiberSum_constant_eq initial (coefficient selected)
          leftRef rightRef))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The actual run's output block retains the same independent seed and full reference density. -/
theorem nativeBatch_run_output_joint_entry (specification : Input N)
    {Reference : Register} (input : Execution.Input base Reference)
    (selected : (resultShape N).Value)
    (left right : (context base noQuantum N).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((run base noQuantum N).finalState Reference input.state).mapClassical
      (run base noQuantum N).output.eval).block selected).matrix
        (left, leftRef) (right, rightRef) =
      if left = restoredSeed base noQuantum N ∧ right = restoredSeed base noQuantum N then
        ((sourceDistribution specification selected).toReal : ℂ) *
          input.state.referenceMarginal.matrix leftRef rightRef
      else 0 :=
  run_output_entry (run base noQuantum N) (restoredSeed base noQuantum N)
    (fun value => ((sourceDistribution specification value).toReal : ℂ))
    (fun {_} {_} _ state value row column refRow refColumn =>
      nativeBatch_output_joint_entry base noQuantum N specification state
        value row column refRow refColumn)
    input.state selected left right leftRef rightRef

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
