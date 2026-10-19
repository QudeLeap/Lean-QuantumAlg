/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import Mathlib.Tactic.IrreducibleDef
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Kernel
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Reference
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.State
import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.State.Readout
import all QuantumAlg.Core.Execution.State.Requirement
import all QuantumAlg.Core.Execution.SelectionAll.Reference

/-!
# Complete reference state at the actual recycled RSA output

Positive execution restores its sole physical bank to the actual reload seed.
The complete stored-reference kernel and a scalar output-weight law then fix
every optional output block jointly with the original external reference.
Impossible outputs have zero mass; no conditional division or reference trace
is used. The target below depends only on the input reference and the physical
seed, independently of a probability calculation or a candidate execution.

The scalar law is an internal bridge premise to be discharged by the actual
finite-source and chronological batch probability proof. It is not an input
condition of the independent state requirement. Zero batches literally execute
the existing empty-result program and use that same program's state proof.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution
open EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- An equivalent private run boundary keeps dependent readout proofs opaque. -/
private irreducible_def sealedPositiveRun (specification : Input N) (laterCount : Nat) :
    AlgorithmRun RecycledModel base (readyContext base noQuantum N (laterCount + 1))
      (LatticeBatchRecoveryOutput.OutputShape N) :=
  positiveRun base noQuantum N specification laterCount

/-- All positive output blocks have the same physical seed and original full reference target. -/
private def positiveStateRequirement (laterCount : Nat) :
    StateRequirement base (readyContext base noQuantum N (laterCount + 1)) :=
  .jointReference Finset.univ
    (.read (.storage (ClassicalFrame.bankWrite noQuantum N (laterCount + 1)
      (ClassicalFrame.selectedRef base N (laterCount + 1))).toCStorageRef))
    (fun Reference input _ => .mixed
      (DensityOperator.observeSelectionWithReference
        (readyContext base noQuantum N (laterCount + 1)).quantumLayout Finset.univ Reference
        (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal))
      ((DensityOperator.observeSelectionWithReference_mass
        (readyContext base noQuantum N (laterCount + 1)).quantumLayout Finset.univ Reference
        (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal)).trans
        (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
          input.state.referenceMarginal
          ((ExecutionState.referenceMarginal_mass input.state).trans input.normalized))))

/-- The literal empty branch preserves the input joint state; positive branches restore the bank
jointly with the complete original reference at every actual optional output. -/
def stateRequirement : (count : Nat) → StateRequirement base (outputContext base noQuantum N count)
  | 0 => NativeFiniteRetry.zeroStateRequirement base N
  | laterCount + 1 => positiveStateRequirement base noQuantum N laterCount

/-- The literal zero-batch program preserves the original full joint state without a seed,
probability premise, or quantum-bank allocation. -/
lemma rsaRecyclingParent_zero_stateRequirement (specification : Input N)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (stateRequirement base noQuantum N 0).Holds input.caller
      ((run base noQuantum N specification 0).finalState environment Reference input.state) :=
  NativeFiniteRetry.zero_stateRequirement_holds base N input

private lemma positive_output_entries (specification : Input N) (laterCount : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification (laterCount + 1)
        (fun stored => weight
          ((positiveRun base noQuantum N specification laterCount).output.eval stored)) original =
        ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (left right : (readyContext base noQuantum N (laterCount + 1)).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((positiveRun base noQuantum N specification laterCount).code.execute environment
      Reference state).mapClassical (fun entry =>
        (positiveRun base noQuantum N specification laterCount).output.eval entry.1)).block
          value).matrix (left, leftRef) (right, rightRef) =
      if left = memberSeed base noQuantum N (laterCount + 1) ∧
          right = memberSeed base noQuantum N (laterCount + 1) then
        ((distribution value).toReal : ℂ) * state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  let code : Circuit RecycledModel base
      (readyContext base noQuantum N (laterCount + 1)) :=
    positiveCode base noQuantum N specification laterCount
  let result : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (RecycledModel.HiddenState × (History × code.Path)) :=
    code.execute environment Reference state
  let read : Store (readyContext base noQuantum N (laterCount + 1)) →
      (LatticeBatchRecoveryOutput.OutputShape N).Value :=
    (positiveRun base noQuantum N specification laterCount).output.eval
  have seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) result :=
    rsaRecyclingParent_positiveCode_seeded base noQuantum N specification laterCount state
  refine BasisSeeded.readout_entry_of_reference
    (source := base) (ctx := readyContext base noQuantum N (laterCount + 1))
    (Reference := Reference) (SourceHistory := RecycledModel.HiddenState × History)
    (History := RecycledModel.HiddenState × (History × code.Path))
    (Outcome := (LatticeBatchRecoveryOutput.OutputShape N).Value)
    state result (memberSeed base noQuantum N (laterCount + 1)) seeded read
    distribution ?_ value left right leftRef rightRef
  intro weight row column
  refine (rsaRecyclingParent_code_referenceFiberSum base noQuantum N specification
    (laterCount + 1) state
    (fun stored => weight (read stored))
    row column).trans ?_
  have weights :
      (fun original : Store base =>
        referenceKernel base noQuantum N specification (laterCount + 1)
          (fun stored => weight (read stored)) original) =
      (fun _ : Store base =>
        ∑ selected : (LatticeBatchRecoveryOutput.OutputShape N).Value,
          ((distribution selected).toReal : ℂ) * weight selected) :=
    funext (constant weight)
  unfold ExecutionState.referenceFiberSum
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro record _
  exact congrArg (fun coefficient : ℂ =>
    coefficient * (state.block record).matrix (basis, row) (basis, column))
    (congr_fun weights record.1)

/-- A history-polymorphic entry law gives the full actual stored-output promise. -/
private lemma run_output_statePromise_of_code_entries
    {model : ExecutionModel} {environment : model.Environment}
    {pre post : RuntimeCtx model.kind} {shape : CShape}
    (program : AlgorithmRun model pre post shape) (seed : post.register.Index)
    (distribution : PMF shape.Value)
    (codeEntries : ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State pre Reference (model.HiddenState × History))
      (value : shape.Value) (left right : post.register.Index)
      (leftRef rightRef : Reference.Index),
      (((program.code.execute environment Reference state).mapClassical
          (fun entry => program.output.eval entry.1)).block value).matrix
          (left, leftRef) (right, rightRef) =
        if left = seed ∧ right = seed then
          ((distribution value).toReal : ℂ) * state.referenceMarginal.matrix leftRef rightRef
        else 0)
    {Reference : Register} (input : OracleInput model.classicalOracles pre Reference)
    (value : shape.Value) :
    (StatePromise.mixed
      (BasisReference.target (R := post.register) seed input.caller.state.referenceMarginal)
      (BasisReference.target_normalized (R := post.register) seed
        input.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass input.caller.state).trans
          input.caller.normalized))).Holds
      (((program.finalState environment Reference input.state).mapClassical
        program.output.eval).block
        value) := by
  refine AlgorithmRun.basisReference_readout_of_executionEntries
    program environment seed distribution ?_ input value
  intro InputReference History historyFintype state _ selected left right leftRef rightRef
  exact codeEntries state selected left right leftRef rightRef

private lemma sealedPositiveRun_code (specification : Input N) (laterCount : Nat) :
    (sealedPositiveRun base noQuantum N specification laterCount).code =
      (positiveRun base noQuantum N specification laterCount).code := by
  rw [sealedPositiveRun_def]

private lemma sealedPositiveRun_output (specification : Input N) (laterCount : Nat) :
    (sealedPositiveRun base noQuantum N specification laterCount).output =
      (positiveRun base noQuantum N specification laterCount).output := by
  rw [sealedPositiveRun_def]

private lemma sealed_positive_output_statePromise
    (specification : Input N) (laterCount : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification (laterCount + 1)
        (fun stored => weight
          ((positiveRun base noQuantum N specification laterCount).output.eval stored)) original =
        ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed
      (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal)
      (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass input.caller.state).trans
          input.caller.normalized))).Holds
      ((((sealedPositiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state).mapClassical
          (sealedPositiveRun base noQuantum N specification laterCount).output.eval).block
        value) := by
  refine run_output_statePromise_of_code_entries
    (sealedPositiveRun base noQuantum N specification laterCount)
    (memberSeed base noQuantum N (laterCount + 1)) distribution ?_ input value
  intro InputReference History historyFintype state selected left right leftRef rightRef
  rw [sealedPositiveRun_code, sealedPositiveRun_output]
  exact positive_output_entries base noQuantum N specification laterCount distribution constant
    state selected left right leftRef rightRef

private lemma sealedPositiveRun_readout_eq (specification : Input N) (laterCount : Nat)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    ((((sealedPositiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state).mapClassical
          (sealedPositiveRun base noQuantum N specification laterCount).output.eval).block value) =
      ((((positiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state).mapClassical
          (positiveRun base noQuantum N specification laterCount).output.eval).block value) := by
  rw [sealedPositiveRun_def]

/-- Every actual positive output has the full seed-reference promise, including zero-mass blocks. -/
private lemma positive_output_statePromise
    (specification : Input N) (laterCount : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification (laterCount + 1)
        (fun stored => weight
          ((positiveRun base noQuantum N specification laterCount).output.eval stored)) original =
        ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference)
    (value : (LatticeBatchRecoveryOutput.OutputShape N).Value) :
    (StatePromise.mixed
      (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal)
      (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
        input.caller.state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass input.caller.state).trans
          input.caller.normalized))).Holds
      ((((positiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state).mapClassical
          (positiveRun base noQuantum N specification laterCount).output.eval).block value) := by
  have canonical := sealed_positive_output_statePromise (environment := environment)
    base noQuantum N specification laterCount
    distribution constant input value
  rw [sealedPositiveRun_readout_eq base noQuantum N specification laterCount input value]
    at canonical
  exact canonical

/-- Assemble the independent complete requirement at the equivalent opaque run. -/
private lemma sealed_positive_stateRequirement
    (specification : Input N) (laterCount : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification (laterCount + 1)
        (fun stored => weight
          ((positiveRun base noQuantum N specification laterCount).output.eval stored)) original =
        ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (stateRequirement base noQuantum N (laterCount + 1)).Holds input.caller
      ((sealedPositiveRun base noQuantum N specification laterCount).finalState environment
        Reference input.state) := by
  intro value
  have canonical := sealed_positive_output_statePromise (environment := environment)
    base noQuantum N specification laterCount
    distribution constant input value
  rw [sealedPositiveRun_output] at canonical
  exact StatePromise.mixed_fullSelection
    (readyContext base noQuantum N (laterCount + 1)).quantumLayout Reference
    (BasisReference.target (memberSeed base noQuantum N (laterCount + 1))
      input.caller.state.referenceMarginal)
    (BasisReference.target_normalized (memberSeed base noQuantum N (laterCount + 1))
      input.caller.state.referenceMarginal
      ((ExecutionState.referenceMarginal_mass input.caller.state).trans input.caller.normalized))
    ((((sealedPositiveRun base noQuantum N specification laterCount).finalState environment
      Reference input.state).mapClassical
        (positiveRun base noQuantum N specification laterCount).output.eval).block value)
    canonical

/-- The actual positive run satisfies the independent joint state requirement once its scalar
output kernel has been identified, for arbitrary incoming Store and external reference. -/
lemma rsaRecyclingParent_positive_stateRequirement_of_kernel
    (specification : Input N) (laterCount : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification (laterCount + 1)
        (fun stored => weight
          ((run base noQuantum N specification (laterCount + 1)).output.eval stored)) original =
        ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (stateRequirement base noQuantum N (laterCount + 1)).Holds input.caller
      ((run base noQuantum N specification (laterCount + 1)).finalState environment Reference
        input.state) := by
  have canonical := sealed_positive_stateRequirement (environment := environment)
    base noQuantum N specification laterCount
    distribution constant input
  have same :
      (sealedPositiveRun base noQuantum N specification laterCount).finalState environment
          Reference input.state =
        (run base noQuantum N specification (laterCount + 1)).finalState environment
          Reference input.state :=
    congrArg
      (fun program : AlgorithmRun RecycledModel base
          (readyContext base noQuantum N (laterCount + 1))
          (LatticeBatchRecoveryOutput.OutputShape N) =>
        program.finalState environment Reference input.state)
      (sealedPositiveRun_def base noQuantum N specification laterCount)
  rw [same] at canonical
  exact canonical

/-- Every natural batch count has the same complete state contract after the actual output-weight
law is supplied; the zero case uses its literal empty program and needs no such premise. -/
lemma rsaRecyclingParent_stateRequirement_of_kernel
    (specification : Input N) (count : Nat)
    (distribution : PMF (LatticeBatchRecoveryOutput.OutputShape N).Value)
    (constant : ∀ (weight : (LatticeBatchRecoveryOutput.OutputShape N).Value → ℂ)
      (original : Store base),
      referenceKernel base noQuantum N specification count
        (fun stored => weight ((run base noQuantum N specification count).output.eval stored))
        original = ∑ value, ((distribution value).toReal : ℂ) * weight value)
    {Reference : Register}
    (input : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (stateRequirement base noQuantum N count).Holds input.caller
      ((run base noQuantum N specification count).finalState environment Reference input.state) :=
        by
  cases count with
  | zero => exact rsaRecyclingParent_zero_stateRequirement base noQuantum N specification input
  | succ laterCount =>
      exact rsaRecyclingParent_positive_stateRequirement_of_kernel base noQuantum N specification
        laterCount distribution constant input

end

end QuantumAlg.Factoring.RSA.Recycling.Program
