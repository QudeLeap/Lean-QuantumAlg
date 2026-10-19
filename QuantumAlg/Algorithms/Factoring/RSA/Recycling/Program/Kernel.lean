/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Reference
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Batch
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Selection
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Allocation
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Observation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Preparation.Observation
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Complete stored-reference kernel of the actual recycled RSA program

The zero-count branch executes its literal retained empty result. Positive
execution initializes the actual frame, draws the first real source before
allocating the sole quantum bank, performs complete measured batches and their
chronological later source draws, then runs the original first-success selector.
The kernel below pulls an arbitrary complete final-Store weight through those
same actual Store transitions and source sums to the original input state.

Every input state and both reference coordinates are admitted. The first seed
comes from actual allocation and loading; subsequent seeds come from actual
reset/reload and are preserved by the real source and recovery instructions.
Recording the initial Store as AlgorithmRun history changes no observation.
These are exact execution laws, without a probability-product assumption or
an additional public input certificate.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The first complete batch, actual later batches, and real selector transport the final weight. -/
private def tailReferenceKernel (input : Input N) (laterCount : Nat)
    (weight : Store (readyContext base noQuantum N (laterCount + 1)) → ℂ) :
    Store (readyContext base noQuantum N (laterCount + 1)) → ℂ :=
  batchBodyReferenceKernel base noQuantum N input (laterCount + 1) 0
    (laterBatchesReferenceKernel base noQuantum N input laterCount
      (fun stored => weight (selectionStore base noQuantum N (laterCount + 1) stored)))

/-- Positive execution draws its first source on the real frame before the actual bank exists. -/
def positiveReferenceKernel (input : Input N) (laterCount : Nat)
    (weight : Store (readyContext base noQuantum N (laterCount + 1)) → ℂ)
    (original : Store base) : ℂ :=
  ∑ value : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      tailReferenceKernel base noQuantum N input laterCount weight
        (PreparationObservation.preparedStore (ClassicalFrame.context base N (laterCount + 1))
          (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
          (sourceStore N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
            (ClassicalFrame.parameterRef base N (laterCount + 1) 0)
            (ClassicalFrame.pushStore base N (laterCount + 1) original) value))

/-- All batch counts use the literal empty-result Store push or the actual positive kernel. -/
def referenceKernel (input : Input N) : (count : Nat) →
    (Store (outputContext base noQuantum N count) → ℂ) → Store base → ℂ
  | 0, weight, original =>
      weight (original.pushRetained base.canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh)
  | laterCount + 1, weight, original =>
      positiveReferenceKernel base noQuantum N input laterCount weight original

private lemma laterSequence_seeded (input : Input N) (count length : Nat)
    (indices : Fin length → Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((Circuit.forRange length fun index =>
        nextBatch base noQuantum N input count (indices index)).execute
          environment Reference state) := by
  induction length generalizing History with
  | zero =>
      rw [Circuit.forRange, Circuit.execute_id_mapClassical]
      exact BasisSeeded.mapStore (memberSeed base noQuantum N count) state seeded id
        (fun entry => (entry.2.1, (entry.2.2, ())))
  | succ length ih =>
      exact BasisSeeded.seq (environment := environment)
        (nextBatch base noQuantum N input count (indices 0))
        (Circuit.forRange length fun index =>
          nextBatch base noQuantum N input count (indices index.succ))
        (memberSeed base noQuantum N count) state
        (ih (fun index => indices index.succ)
          ((nextBatch base noQuantum N input count (indices 0)).execute environment Reference state)
          (rsaRecyclingParent_nextBatch_seeded base noQuantum N input count (indices 0) state))

/-- The literal chronological later-batch suffix preserves the bank, including its empty case. -/
lemma rsaRecyclingParent_laterBatches_seeded (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1))
      ((Circuit.forRange laterCount fun index =>
        nextBatch base noQuantum N input (laterCount + 1) index.succ).execute
          environment Reference state) :=
  laterSequence_seeded base noQuantum N input (laterCount + 1) laterCount Fin.succ state seeded

/-- Actual positive execution establishes its final seed without an input seed premise. -/
lemma rsaRecyclingParent_positiveCode_seeded (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1))
      ((positiveCode base noQuantum N input laterCount).execute environment Reference state) := by
  let allocated : Circuit RecycledModel base
      (ClassicalFrame.context base N (laterCount + 1)) :=
    ClassicalFrame.allocate base N (laterCount + 1)
  let drawn : Circuit RecycledModel (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.context base N (laterCount + 1)) := firstSource base N laterCount
  let prepared : Circuit RecycledModel (ClassicalFrame.context base N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let completed : Circuit RecycledModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    batchBody base noQuantum N input (laterCount + 1) 0
  let later : Circuit RecycledModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    Circuit.forRange laterCount fun index =>
      nextBatch base noQuantum N input (laterCount + 1) index.succ
  let chosen : Circuit RecycledModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    select base noQuantum N (laterCount + 1)
  refine BasisSeeded.seq (environment := environment) allocated
    (drawn.seq (prepared.seq (completed.seq (later.seq chosen)))) _ state ?_
  refine BasisSeeded.seq (environment := environment)
    drawn (prepared.seq (completed.seq (later.seq chosen))) _ _ ?_
  refine BasisSeeded.seq (environment := environment)
    prepared (completed.seq (later.seq chosen)) _ _ ?_
  refine BasisSeeded.seq (environment := environment) completed (later.seq chosen) _ _ ?_
  refine BasisSeeded.seq (environment := environment) later chosen _ _ ?_
  exact rsaRecyclingParent_select_seeded base noQuantum N (laterCount + 1)
    (memberSeed base noQuantum N (laterCount + 1)) _
    (rsaRecyclingParent_laterBatches_seeded base noQuantum N input laterCount _
      (rsaRecyclingParent_batchBody_seeded base noQuantum N input (laterCount + 1) 0 _))

private lemma tail_referenceFiberSum (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state)
    (weight : Store (readyContext base noQuantum N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((batchBody base noQuantum N input (laterCount + 1) 0).seq
        ((Circuit.forRange laterCount fun index =>
          nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
            (select base noQuantum N (laterCount + 1)))).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => tailReferenceKernel base noQuantum N input laterCount weight entry.1)
        left right := by
  rw [Circuit.referenceFiberSum_execute_seq, Circuit.referenceFiberSum_execute_seq]
  refine (rsaRecyclingParent_select_referenceFiberSum base noQuantum N (laterCount + 1)
    _ weight left right).trans ?_
  refine (rsaRecyclingParent_laterBatches_referenceFiberSum base noQuantum N input laterCount _
    (rsaRecyclingParent_batchBody_seeded base noQuantum N input (laterCount + 1) 0 state)
    (fun stored => weight (selectionStore base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  exact rsaRecyclingParent_batchBody_referenceFiberSum base noQuantum N input (laterCount + 1) 0
    state seeded (laterBatchesReferenceKernel base noQuantum N input laterCount
      (fun stored => weight (selectionStore base noQuantum N (laterCount + 1) stored))) left right

/-- Positive actual execution pulls every complete-Store/reference weight to its original input. -/
lemma rsaRecyclingParent_positiveCode_referenceFiberSum (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (readyContext base noQuantum N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((positiveCode base noQuantum N input laterCount).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => positiveReferenceKernel base noQuantum N input laterCount weight entry.1)
        left right := by
  let allocated : Circuit RecycledModel base
      (ClassicalFrame.context base N (laterCount + 1)) :=
    ClassicalFrame.allocate base N (laterCount + 1)
  let drawn : Circuit RecycledModel (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.context base N (laterCount + 1)) := firstSource base N laterCount
  let prepared : Circuit RecycledModel (ClassicalFrame.context base N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let tail : Circuit RecycledModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    (batchBody base noQuantum N input (laterCount + 1) 0).seq
      ((Circuit.forRange laterCount fun index =>
        nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
          (select base noQuantum N (laterCount + 1)))
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment) allocated
    (drawn.seq (prepared.seq tail)) state weight left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment)
    drawn (prepared.seq tail)
    (allocated.execute environment Reference state) weight left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment) prepared tail
    (drawn.execute
      environment Reference (allocated.execute
        environment Reference state)) weight left right).trans ?_
  refine (tail_referenceFiberSum base noQuantum N input laterCount _
    (InitialSeed.recyclingPrepare_seeded (ClassicalFrame.context base N (laterCount + 1))
      (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N _) weight left right).trans ?_
  refine (PreparationObservation.prepare_referenceFiberSum_store
    (ClassicalFrame.context base N (laterCount + 1))
    (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N _
    (tailReferenceKernel base noQuantum N input laterCount weight) left right).trans ?_
  refine (rsaRecyclingParent_source_referenceFiberSum N
    (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (ClassicalFrame.parameterRef base N (laterCount + 1) 0) _
    (fun stored => tailReferenceKernel base noQuantum N input laterCount weight
      (PreparationObservation.preparedStore (ClassicalFrame.context base N (laterCount + 1))
        (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) stored)) left right).trans ?_
  exact ClassicalFrame.rsaRecyclingFrame_allocate_referenceFiberSum base N (laterCount + 1) state
    (fun stored => ∑ value : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        tailReferenceKernel base noQuantum N input laterCount weight
          (PreparationObservation.preparedStore (ClassicalFrame.context base N (laterCount + 1))
            (ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
            (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
            (sourceStore N (ClassicalFrame.sampleRef base N (laterCount + 1) 0)
              (ClassicalFrame.parameterRef base N (laterCount + 1) 0) stored value))) left right

/-- Every actual code branch, including the literal zero-count program, has the same kernel law. -/
lemma rsaRecyclingParent_code_referenceFiberSum (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (outputContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((run base noQuantum N input count).code.execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => referenceKernel base noQuantum N input count weight entry.1)
        left right := by
  cases count with
  | zero =>
      change ExecutionState.referenceFiberSum
        ((NativeRetryEmpty.code base N).execute environment Reference state)
        (fun entry _ => weight entry.1) left right = _
      rw [NativeRetryEmpty.code_execute]
      exact ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1.pushRetained base.canonicalFreshKey
          (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh,
            (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight entry.1) left right
  | succ laterCount =>
      exact rsaRecyclingParent_positiveCode_referenceFiberSum base noQuantum N input laterCount
        state weight left right

/-- Recording the original Store as actual run history preserves the complete weighted kernel. -/
lemma rsaRecyclingParent_run_referenceFiberSum (input : Input N) (count : Nat)
    {Reference : Register}
    (state : ExecutionState (Store base × ShortDLP.CompiledMAU.Recycling.model.HiddenState)
      (Register.prod base.register Reference))
    (weight : Store (outputContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((run base noQuantum N input count).execute
      environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => referenceKernel base noQuantum N input count weight entry.1)
        left right := by
  change ExecutionState.referenceFiberSum
    ((run base noQuantum N input count).code.execute environment Reference
      (state.mapClassical (fun entry => (entry.1, (entry.2, entry.1)))))
    (fun entry _ => weight entry.1) left right = _
  refine (rsaRecyclingParent_code_referenceFiberSum base noQuantum N input count _
    weight left right).trans ?_
  exact ExecutionState.referenceFiberSum_mapClassical state
    (fun entry => (entry.1, (entry.2, entry.1)))
    (fun entry _ => referenceKernel base noQuantum N input count weight entry.1) left right

end

end QuantumAlg.Factoring.RSA.Recycling.Program
