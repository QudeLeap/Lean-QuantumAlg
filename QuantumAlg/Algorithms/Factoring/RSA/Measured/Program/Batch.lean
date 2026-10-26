/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members.Admission
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Recovery.Transport
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation

/-!
# Complete actual fresh-source batches on the measured bank

The real uniform source establishes its own parameter condition. Configured
actual members preserve it and establish the bank seed before the complete
paid recovery. Every kernel below follows those same chronological programs,
with the complete original parent Store and both Reference indices
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- Original packed destinations are the exact structural operands of the real recovery. -/
def parentTerminals (batch : Fin count) :
    LatticePairRecoveryBatch.Terminals (Recycling.ClassicalFrame.context base N count) N
      configuration.additionalMembers :=
  fun index => FirstAccepted.cellRead (Recycling.ClassicalFrame.packedRef base N count batch index)

/-- The original complete all-pairs value is written into its own parent factor destination. -/
def recoveryParentStore (batch : Fin count)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    Store (Recycling.ClassicalFrame.context base N count) :=
  stored.write (Recycling.ClassicalFrame.factorRef base N count batch)
    (LatticeFixedBatchRecoveryMachine.batchValue
      (sourceStoredSample
        (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch)) stored)
      (parentTerminals base N count batch) stored)

/-- Real configured member kernels precede the same original complete recovery write. -/
def batchBodyParentReferenceKernel (batch : Fin count)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ) :
    Store (Recycling.ClassicalFrame.context base N count) → ℂ :=
  membersParentReferenceKernel base N count batch
    (fun stored => weight (recoveryParentStore base N count batch stored))

/-- A later actual batch draws its source after the preceding complete bank execution. -/
def nextBatchParentReferenceKernel (batch : Fin count)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) : ℂ :=
  ∑ value : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      batchBodyParentReferenceKernel base N count batch weight
        (sourceStore N (Recycling.ClassicalFrame.sampleRef base N count batch)
          (Recycling.ClassicalFrame.parameterRef base N count batch) stored value)

/-- Existing actual recovery has the original complete parent write on its real source support. -/
lemma rsaMeasuredParent_recover_parent_referenceFiberSum (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (admitted : ∀ record, 0 < (state.block record).mass →
      batchSourceAgreement base N count input batch
        (parentStoreAt base noQuantum N count record.1))
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((recover base noQuantum N input count batch).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (recoveryParentStore base N count batch
          (parentStoreAt base noQuantum N count entry.1))) left right :=
  rsaMeasuredParent_recovery_parent_referenceFiberSum
    (parentTransport (Recycling.ClassicalFrame.context base N count)
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) input
    (sourceStoredSample
      (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch)))
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))
    (parentTerminals base N count batch) (Recycling.ClassicalFrame.factorRef base N count batch)
    environment state admitted weight left right

/-- All actual members and paid recovery compose one complete parent/reference kernel. -/
lemma rsaMeasuredParent_batchBody_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (admitted : ∀ record, 0 < (state.block record).mass →
      batchSourceAgreement base N count input batch
        (parentStoreAt base noQuantum N count record.1))
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((batchBody base noQuantum N input count batch).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => batchBodyParentReferenceKernel base N count batch weight
          (parentStoreAt base noQuantum N count entry.1)) left right := by
  refine (Circuit.referenceFiberSum_execute_seq
    (members base noQuantum N input count batch) (recover base noQuantum N input count batch)
    environment state (fun stored => weight (parentStoreAt base noQuantum N count stored))
    left right).trans ?_
  refine (rsaMeasuredParent_recover_parent_referenceFiberSum base noQuantum N count input batch
    environment ((members base noQuantum N input count batch).execute environment Reference state)
    (rsaMeasuredParent_members_admitted base noQuantum N count input batch environment state seeded
      admitted) weight left right).trans ?_
  exact rsaMeasuredParent_members_parent_referenceFiberSum base noQuantum N input count batch
    environment state seeded (fun stored => weight (recoveryParentStore base N count batch stored))
    left right

/-- Classical recovery preserves the actual seed supplied by the complete member bank. -/
lemma rsaMeasuredParent_batchBody_seeded (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((batchBody base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (members base noQuantum N input count batch)
    (recover base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaMeasuredParent_recover_seeded (environment := environment) base noQuantum input count batch
      (memberSeed base noQuantum N count) _
      (rsaMeasuredParent_members_seeded base noQuantum N input count batch environment state
        seeded))

/-- A real later source preserves the complete physical seed on its same existing bank. -/
lemma rsaMeasuredParent_nextSource_seeded (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((nextSource base noQuantum N count batch).execute environment Reference state) :=
  rsaMeasuredParent_source_seeded (environment := environment) N
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.sampleRef base N count batch))
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.parameterRef base N count batch))
    (memberSeed base noQuantum N count) state seeded

/-- Actual later execution combines its fresh source with the complete same-bank batch kernel. -/
lemma rsaMeasuredParent_nextBatch_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextBatch base noQuantum N input count batch).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => nextBatchParentReferenceKernel base N count batch weight
          (parentStoreAt base noQuantum N count entry.1)) left right := by
  refine (Circuit.referenceFiberSum_execute_seq (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) environment state
    (fun stored => weight (parentStoreAt base noQuantum N count stored)) left right).trans ?_
  refine (rsaMeasuredParent_batchBody_parent_referenceFiberSum base noQuantum N count input batch
    environment ((nextSource base noQuantum N count batch).execute environment Reference state)
    (rsaMeasuredParent_nextSource_seeded base noQuantum N count batch environment state seeded)
    (rsaMeasuredParent_nextSource_admitted base noQuantum N count input batch environment state)
    weight left right).trans ?_
  exact rsaMeasuredParent_source_parent_referenceFiberSum (environment := environment) N
    (parentTransport (Recycling.ClassicalFrame.context base N count)
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (Recycling.ClassicalFrame.sampleRef base N count batch)
    (Recycling.ClassicalFrame.parameterRef base N count batch) input state
    (batchBodyParentReferenceKernel base N count batch weight) left right

/-- Every actual fresh-source batch retains the seed established by preceding execution. -/
lemma rsaMeasuredParent_nextBatch_seeded (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((nextBatch base noQuantum N input count batch).execute environment Reference state) :=
  BasisSeeded.seq (environment := environment) (nextSource base noQuantum N count batch)
    (batchBody base noQuantum N input count batch) (memberSeed base noQuantum N count) state
    (rsaMeasuredParent_batchBody_seeded base noQuantum N count input batch environment _
      (rsaMeasuredParent_nextSource_seeded base noQuantum N count batch environment state seeded))

end

end QuantumAlg.Factoring.RSA.Measured.Program
