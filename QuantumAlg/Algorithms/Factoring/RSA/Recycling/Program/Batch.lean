/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Reference
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Recovery
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Source
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Kernel

/-!
# Actual RSA batch and chronological fresh-source reference kernels

A complete batch executes the actual sixteen recycled members and the
original fixed-batch recovery. Its weighted-reference kernel composes the
member kernel with the real caller Store returned by recovery. A later batch
first performs its native fresh source draw on the same allocated bank; its
kernel sums over the exact returned sourceStore, including the actual stored
sample and parameter. All observations keep the entire Store and two arbitrary
reference coordinates, with no independence assumption on incoming records.

The actual members establish the bank seed unconditionally and recovery
preserves it. The real source preserves an established seed for the next batch.
The finite later-batch kernel follows the precise increasing sequence in the
parent program; it does not replace chronological source draws by a joint draw.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical
open scoped BigOperators

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Backward observation of the real members followed by their full allocated batch recovery. -/
def batchBodyReferenceKernel (input : Input N) (count : Nat) (batch : Fin count)
    (weight : Store (readyContext base noQuantum N count) → ℂ) :
    Store (readyContext base noQuantum N count) → ℂ :=
  membersReferenceKernel base noQuantum N count batch
    (fun stored => weight (recoveryStore base noQuantum input count batch stored))

/-- A later batch averages its observation over the real fresh source and actual returned Store. -/
def nextBatchReferenceKernel (input : Input N) (count : Nat) (batch : Fin count)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (original : Store (readyContext base noQuantum N count)) : ℂ :=
  ∑ value : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      batchBodyReferenceKernel base noQuantum N input count batch weight
        (sourceStore N
          (ClassicalFrame.bankWrite noQuantum N count
            (ClassicalFrame.sampleRef base N count batch))
          (ClassicalFrame.bankWrite noQuantum N count
            (ClassicalFrame.parameterRef base N count batch)) original value)

/-- The actual parent suffix processes later batch indices in their original increasing order. -/
def laterBatchesReferenceKernel (input : Input N) (laterCount : Nat) :
    (Store (readyContext base noQuantum N (laterCount + 1)) → ℂ) →
      Store (readyContext base noQuantum N (laterCount + 1)) → ℂ :=
  Circuit.forRangeReferenceKernel laterCount
    (fun index => nextBatchReferenceKernel base noQuantum N input (laterCount + 1) index.succ)

/-- Actual members reset the bank before recovery, so no incoming seed premise is needed. -/
lemma rsaRecyclingParent_batchBody_seeded (input : Input N) (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((batchBody base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (members base noQuantum N count batch)
    (recover base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaRecyclingParent_recover_seeded base noQuantum input count batch
      (memberSeed base noQuantum N count)
      ((members base noQuantum N count batch).execute environment Reference state)
      (rsaRecyclingParent_members_seeded base noQuantum N count batch state))

/-- The complete batch transports every full-Store/reference observation through real recovery. -/
lemma rsaRecyclingParent_batchBody_referenceFiberSum (input : Input N)
    (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((batchBody base noQuantum N input count batch).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => batchBodyReferenceKernel base noQuantum N input count batch weight entry.1)
        left right :=
  (Circuit.referenceFiberSum_execute_seq (environment := environment)
    (members base noQuantum N count batch)
    (recover base noQuantum N input count batch) state weight left right).trans
    ((rsaRecyclingParent_recover_referenceFiberSum base noQuantum input count batch
      ((members base noQuantum N count batch).execute
        environment Reference state) weight left right).trans
      (rsaRecyclingParent_members_referenceFiberSum base noQuantum N input count batch state seeded
        (fun stored => weight (recoveryStore base noQuantum input count batch stored)) left right))

/-- The actual fresh draw and parameter computation preserve the previously restored bank. -/
lemma rsaRecyclingParent_nextSource_seeded (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((nextSource base noQuantum N count batch).execute environment Reference state) :=
  rsaRecyclingParent_source_seeded N
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.parameterRef base N count batch))
    (memberSeed base noQuantum N count) state seeded

/-- A complete actual later batch restores the bank for every incoming mixed caller state. -/
lemma rsaRecyclingParent_nextBatch_seeded (input : Input N) (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((nextBatch base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaRecyclingParent_batchBody_seeded base noQuantum N input count batch
      ((nextSource base noQuantum N count batch).execute environment Reference state))

/-- The next batch's full kernel includes its own actual uniform draw before any member executes. -/
lemma rsaRecyclingParent_nextBatch_referenceFiberSum (input : Input N)
    (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((nextBatch base noQuantum N input count batch).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => nextBatchReferenceKernel base noQuantum N input count batch weight entry.1)
        left right :=
  (Circuit.referenceFiberSum_execute_seq (environment := environment)
    (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) state weight left right).trans
    ((rsaRecyclingParent_batchBody_referenceFiberSum base noQuantum N input count batch
      ((nextSource base noQuantum N count batch).execute environment Reference state)
      (rsaRecyclingParent_nextSource_seeded base noQuantum N count batch state seeded)
      weight left right).trans
      (rsaRecyclingParent_source_referenceFiberSum N
        (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.sampleRef base N count batch))
        (ClassicalFrame.bankWrite noQuantum N count
          (ClassicalFrame.parameterRef base N count batch))
        state (batchBodyReferenceKernel base noQuantum N input count batch weight) left right))

/-- The literal later-batch suffix composes chronological fresh-source kernels, including zero. -/
lemma rsaRecyclingParent_laterBatches_referenceFiberSum (input : Input N) (laterCount : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state)
    (weight : Store (readyContext base noQuantum N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.forRange laterCount fun index =>
          nextBatch base noQuantum N input (laterCount + 1) index.succ).execute
            environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ =>
          laterBatchesReferenceKernel base noQuantum N input laterCount weight entry.1)
        left right :=
  Circuit.forRange_referenceFiberSum (environment := environment) laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    (memberSeed base noQuantum N (laterCount + 1))
    (fun index => nextBatchReferenceKernel base noQuantum N input (laterCount + 1) index.succ)
    (fun index _ _ _ actual =>
      rsaRecyclingParent_nextBatch_seeded base noQuantum N input (laterCount + 1) index.succ actual)
    (fun index _ _ _ actual supported observation first second =>
      rsaRecyclingParent_nextBatch_referenceFiberSum base noQuantum N input
        (laterCount + 1) index.succ actual supported observation first second)
    state seeded weight left right

/-- Actual allocation and loading supply the first batch's seed without a caller premise. -/
lemma rsaRecyclingParent_prepare_batchBody_referenceFiberSum (input : Input N)
    (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (ClassicalFrame.context base N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N count)
        (ClassicalFrame.frameNoQuantum base noQuantum N count)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).seq
          (batchBody base noQuantum N input count batch)).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum
        ((ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N count)
          (ClassicalFrame.frameNoQuantum base noQuantum N count)
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).execute
            environment Reference state)
        (fun entry _ => batchBodyReferenceKernel base noQuantum N input count batch weight entry.1)
        left right := by
  let prepared : Circuit RecycledModel (ClassicalFrame.context base N count)
      (readyContext base noQuantum N count) :=
    ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let completed : Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) := batchBody base noQuantum N input count batch
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment)
    prepared completed state weight left right).trans ?_
  exact rsaRecyclingParent_batchBody_referenceFiberSum base noQuantum N input count batch _
    (ShortDLP.CompiledMAU.Recycling.InitialSeed.recyclingPrepare_seeded
      (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N state) weight left right

end

end QuantumAlg.Factoring.RSA.Recycling.Program
