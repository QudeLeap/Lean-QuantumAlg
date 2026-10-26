/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Allocation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Output.Layout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Semantics
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Context
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Complete Store observations of the actual retained RSA frame

The four actual allocators contain only retention, identity and sequencing.
Their Store maps below follow those same chronological initialized pushes.
Every complex weight on the entire resulting Store is transported to the
original Store with both external-reference indices intact. No source sample
is drawn during this allocation and no quantum bank is introduced here.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame

noncomputable section

variable [configuration : Configuration]

open Execution ShortDLP.CompiledMAU
open EkeraHastadStyle.Canonical

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

/-- The actual packed-cell allocator initializes its destinations in chronological order. -/
private def pushPacked (m ell width : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Store base → Store (RuntimeResults.context m ell width base count)
  | _, 0, original => original
  | base, count + 1, original =>
      pushPacked m ell width (RuntimeResults.next m ell width base) count
        (original.pushRetained base.canonicalFreshKey (.bits (RuntimeRound.resultBits m ell width))
          base.canonicalFreshKey_fresh)

/-- One actual batch frame adjoins its source pair, configured result cells and factor cell. -/
private def pushBatch (base : RuntimeCtx .quantum) (N : Nat) (original : Store base) :
    Store (batch base N) :=
  (pushPacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N) membersPerBatch
    (ShorStyle.Canonical.Sampler.Retained.pushStore N original)).pushRetained
      (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
      (outcomes base N).canonicalFreshKey_fresh

/-- The actual batch-frame recursion initializes each batch before its successor. -/
private def pushBatches (N : Nat) : (base : RuntimeCtx .quantum) → (count : Nat) →
    Store base → Store (batches N base count)
  | _, 0, original => original
  | base, count + 1, original =>
      pushBatches N (batch base N) count (pushBatch base N original)

/-- The complete actual frame retains its final selected-factor cell after all batch frames. -/
def pushStore (base : RuntimeCtx .quantum) (N count : Nat) (original : Store base) :
    Store (context base N count) :=
  (pushBatches N base count original).pushRetained
    (batches N base count).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    (batches N base count).canonicalFreshKey_fresh

omit configuration in
private lemma allocatePacked_referenceFiberSum (m ell width : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (RuntimeResults.context m ell width base count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((allocatePacked m ell width base count).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (pushPacked m ell width base count entry.1)) left right := by
  induction count generalizing base History with
  | zero =>
      have executed := Circuit.execute_id_mapClassical (environment := environment)
        (model := ShortDLP.CompiledMAU.Recycling.model) (allowAllocation := true) Reference state
      have observed := congrArg (fun output => ExecutionState.referenceFiberSum output
        (fun entry _ => weight entry.1) left right) executed
      exact observed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight entry.1) left right)
  | succ count ih =>
      let first : Circuit ShortDLP.CompiledMAU.Recycling.model base
          (RuntimeResults.next m ell width base) :=
        Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model) base base.canonicalFreshKey
          (.bits (RuntimeRound.resultBits m ell width)) base.canonicalFreshKey_fresh
      let second : Circuit ShortDLP.CompiledMAU.Recycling.model
          (RuntimeResults.next m ell width base)
          (RuntimeResults.context m ell width (RuntimeResults.next m ell width base) count) :=
        allocatePacked m ell width (RuntimeResults.next m ell width base) count
      refine (Circuit.referenceFiberSum_execute_seq (environment := environment) first second
        state weight left right).trans ?_
      refine (ih (RuntimeResults.next m ell width base)
        (first.execute environment Reference state) weight).trans ?_
      exact Circuit.referenceFiberSum_execute_retain (environment := environment)
        (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := BitWord.model) (classicalOracles := .empty) base.canonicalFreshKey
        (.bits (RuntimeRound.resultBits m ell width)) base.canonicalFreshKey_fresh state
        (fun stored => weight (pushPacked m ell width
          (RuntimeResults.next m ell width base) count stored)) left right

private lemma allocateBatch_referenceFiberSum (base : RuntimeCtx .quantum) (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (batch base N) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocateBatch base N).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (pushBatch base N entry.1)) left right := by
  let source : Circuit ShortDLP.CompiledMAU.Recycling.model base (sampled base N) :=
    ShorStyle.Canonical.Sampler.Retained.allocation
      (model := ShortDLP.CompiledMAU.Recycling.model) base N
  let packed : Circuit ShortDLP.CompiledMAU.Recycling.model (sampled base N) (outcomes base N) :=
    allocatePacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampled base N)
      membersPerBatch
  let result : Circuit ShortDLP.CompiledMAU.Recycling.model (outcomes base N) (batch base N) :=
    Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
      (outcomes base N) (outcomes base N).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh
  let packedWeight : Store (outcomes base N) → ℂ := fun stored =>
    weight (stored.pushRetained (outcomes base N).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (outcomes base N).canonicalFreshKey_fresh)
  let sourceWeight : Store (sampled base N) → ℂ := fun stored =>
    packedWeight (pushPacked (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (sampled base N) membersPerBatch stored)
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment) source
    (packed.seq result)
    state weight left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment) packed result
    (source.execute environment Reference state) weight left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_retain (environment := environment)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := .empty)
    (outcomes base N).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    (outcomes base N).canonicalFreshKey_fresh
    (packed.execute environment Reference (source.execute environment Reference state)) weight
      left right).trans ?_
  refine (allocatePacked_referenceFiberSum (shortLogBits N) (tradeoffBits N)
    (arithmeticBits N) (sampled base N) membersPerBatch
    (source.execute environment Reference state) packedWeight left right).trans ?_
  have executed := ShorStyle.Canonical.Sampler.Retained.samplerRetained_allocation_execute
    (environment := environment)
    (model := ShortDLP.CompiledMAU.Recycling.model) base N Reference state
  have observed := congrArg (fun output => ExecutionState.referenceFiberSum output
    (fun entry _ => sourceWeight entry.1) left right) executed
  exact observed.trans (ExecutionState.referenceFiberSum_mapClassical state
    (fun entry => (ShorStyle.Canonical.Sampler.Retained.pushStore N entry.1,
      (entry.2.1, (entry.2.2, ((), ())))))
    (fun entry _ => sourceWeight entry.1) left right)

private lemma allocateBatches_referenceFiberSum (N : Nat)
    (base : RuntimeCtx .quantum) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (batches N base count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocateBatches N base count).execute environment
      Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (pushBatches N base count entry.1)) left right := by
  induction count generalizing base History with
  | zero =>
      have executed := Circuit.execute_id_mapClassical (environment := environment)
        (model := ShortDLP.CompiledMAU.Recycling.model) (allowAllocation := true) Reference state
      have observed := congrArg (fun output => ExecutionState.referenceFiberSum output
        (fun entry _ => weight entry.1) left right) executed
      exact observed.trans (ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight entry.1) left right)
  | succ count ih =>
      let first := allocateBatch base N
      let second := allocateBatches N (batch base N) count
      refine (Circuit.referenceFiberSum_execute_seq (environment := environment) first second
        state weight left right).trans ?_
      refine (ih (batch base N) (first.execute environment Reference state) weight).trans ?_
      exact allocateBatch_referenceFiberSum base N state
        (fun stored => weight (pushBatches N (batch base N) count stored)) left right

/-- Every frame weight pulls back through its real initialized Store with the reference intact. -/
lemma rsaRecyclingFrame_allocate_referenceFiberSum (base : RuntimeCtx .quantum) (N count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (weight : Store (context base N count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((allocate base N count).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (pushStore base N count entry.1)) left right := by
  let first := allocateBatches N base count
  let second : Circuit ShortDLP.CompiledMAU.Recycling.model
      (batches N base count) (context base N count) :=
    Circuit.retain (model := ShortDLP.CompiledMAU.Recycling.model)
      (batches N base count) (batches N base count).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment) first second
    state weight left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_retain (environment := environment)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (operations := BitWord.model) (classicalOracles := .empty)
    (batches N base count).canonicalFreshKey (LatticeBatchRecoveryOutput.OutputShape N)
    (batches N base count).canonicalFreshKey_fresh
    (first.execute environment Reference state) weight left right).trans ?_
  exact allocateBatches_referenceFiberSum N base count state
    (fun stored => weight (stored.pushRetained (batches N base count).canonicalFreshKey
      (LatticeBatchRecoveryOutput.OutputShape N) (batches N base count).canonicalFreshKey_fresh))
    left right

end

end QuantumAlg.Factoring.RSA.Recycling.ClassicalFrame
