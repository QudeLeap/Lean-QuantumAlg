/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Batch.Seed
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Selection
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Initialization
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Observation
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Chronological complete-parent kernels of the actual measured RSA suffix

The first actual batch is followed by exactly the configured later native
source/batch programs and then the real first-populated selector. Complete
original parent Stores and both Reference coordinates remain in every law
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every later actual batch uses its own original fresh-source parent kernel in order. -/
def laterBatchesParentReferenceKernel (laterCount : Nat)
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ) :
    Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ :=
  Circuit.forRangeReferenceKernel laterCount
    (fun index => nextBatchParentReferenceKernel base N (laterCount + 1) index.succ) weight

/-- The actual first batch, complete later suffix and native selector transport the final weight. -/
def tailParentReferenceKernel (laterCount : Nat)
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ) :
    Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ :=
  batchBodyParentReferenceKernel base N (laterCount + 1) 0
    (laterBatchesParentReferenceKernel base N laterCount
      (fun stored => weight (parentSelectionStore base N (laterCount + 1) stored)))

/-- Real chronological later batches compose their own complete parent/reference kernels. -/
lemma rsaMeasuredParent_laterBatches_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state)
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Circuit.forRange laterCount fun index =>
        nextBatch base noQuantum N input (laterCount + 1) index.succ).execute
          environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N (laterCount + 1) entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => laterBatchesParentReferenceKernel base N laterCount weight
          (parentStoreAt base noQuantum N (laterCount + 1) entry.1)) left right :=
  measuredForRange_parent_referenceFiberSum
    (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) laterCount
    (fun index => nextBatch base noQuantum N input (laterCount + 1) index.succ)
    environment (memberSeed base noQuantum N (laterCount + 1))
    (fun index => nextBatchParentReferenceKernel base N (laterCount + 1) index.succ)
    (fun index _ _ _ actual => rsaMeasuredParent_nextBatch_seeded_any base noQuantum N
      (laterCount + 1) input index.succ environment actual)
    (fun index _ _ _ actual supported observation first second =>
      rsaMeasuredParent_nextBatch_parent_referenceFiberSum base noQuantum N (laterCount + 1)
        input index.succ environment actual supported observation first second)
    state seeded weight left right

/-- The actual initialized suffix transports every original parent/reference observation. -/
lemma rsaMeasuredParent_tail_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N (laterCount + 1)) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N (laterCount + 1)) state)
    (admitted : ∀ record, 0 < (state.block record).mass →
      batchSourceAgreement base N (laterCount + 1) input 0
        (parentStoreAt base noQuantum N (laterCount + 1) record.1))
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      (((batchBody base noQuantum N input (laterCount + 1) 0).seq
        ((Circuit.forRange laterCount fun index =>
          nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
            (select base noQuantum N (laterCount + 1)))).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N (laterCount + 1) entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => tailParentReferenceKernel base N laterCount weight
          (parentStoreAt base noQuantum N (laterCount + 1) entry.1)) left right := by
  let first := batchBody base noQuantum N input (laterCount + 1) 0
  let later := Circuit.forRange laterCount fun index =>
    nextBatch base noQuantum N input (laterCount + 1) index.succ
  let chosen := select base noQuantum N (laterCount + 1)
  refine (Circuit.referenceFiberSum_execute_seq first (later.seq chosen) environment state
    (fun stored => weight (parentStoreAt base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq later chosen environment
    (first.execute environment Reference state)
    (fun stored => weight (parentStoreAt base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  refine (rsaMeasuredParent_select_parent_referenceFiberSum (environment := environment)
    base noQuantum N (laterCount + 1)
    (later.execute environment Reference (first.execute environment Reference state))
    weight left right).trans ?_
  refine (rsaMeasuredParent_laterBatches_parent_referenceFiberSum base noQuantum N input laterCount
    environment (first.execute environment Reference state)
    (rsaMeasuredParent_batchBody_seeded_any base noQuantum N (laterCount + 1) input 0
      environment state)
    (fun stored => weight (parentSelectionStore base N (laterCount + 1) stored))
    left right).trans ?_
  exact rsaMeasuredParent_batchBody_parent_referenceFiberSum base noQuantum N (laterCount + 1)
    input 0 environment state seeded admitted
    (laterBatchesParentReferenceKernel base N laterCount
      (fun stored => weight (parentSelectionStore base N (laterCount + 1) stored))) left right

end

end QuantumAlg.Factoring.RSA.Measured.Program
