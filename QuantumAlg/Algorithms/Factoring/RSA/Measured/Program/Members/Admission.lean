/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Source.Agreement
import all QuantumAlg.Core.Execution.Reference.Admission

/-!
# The real configured member bank preserves actual source agreement

Native source execution establishes the recovery input condition on every
positive actual record. Distinct real packed destinations preserve both
source operands. Complete conditional parent/reference kernels then preserve
that condition through all configured members [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The original recovery entry condition is read only from the same actual parent source cells. -/
def batchSourceAgreement (input : Input N) (batch : Fin count)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) : Prop :=
  SourceAgreement input
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch))
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch)) stored

/-- Every positive actual fresh draw establishes its own complete batch source condition. -/
lemma rsaMeasuredParent_nextSource_admitted (input : Input N) (batch : Fin count)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    ∀ record, 0 < (((nextSource base noQuantum N count batch).execute
      environment Reference state).block record).mass →
      batchSourceAgreement base N count input batch
        (parentStoreAt base noQuantum N count record.1) :=
  rsaMeasuredParent_source_parent_admitted
    (parentTransport (Recycling.ClassicalFrame.context base N count)
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (Recycling.ClassicalFrame.sampleRef base N count batch)
    (Recycling.ClassicalFrame.parameterRef base N count batch) input
    (Recycling.ClassicalFrame.rsaRecyclingFrame_sample_parameter_separate
      base N count batch batch).symm
    environment state

private lemma memberKernel_zero_on_agreement (input : Input N) (batch : Fin count)
    (index : Fin membersPerBatch)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (zero : ∀ stored, batchSourceAgreement base N count input batch stored → weight stored = 0)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (agrees : batchSourceAgreement base N count input batch stored) :
    memberParentReferenceKernel base N count batch index weight stored = 0 := by
  unfold memberParentReferenceKernel
  apply Finset.sum_eq_zero
  intro terminal _
  have written := rsaMeasuredParent_sourceAgreement_write input
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.sampleRef base N count batch))
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))
    (Recycling.ClassicalFrame.packedRef base N count batch index) (.bits terminal) stored
    (fun present =>
      Recycling.ClassicalFrame.rsaRecyclingFrame_packed_sample_separate
        base N count batch batch index (List.mem_singleton.mp present))
    (fun present =>
      Recycling.ClassicalFrame.rsaRecyclingFrame_packed_parameter_separate
        base N count batch batch index (List.mem_singleton.mp present)) agrees
  rw [zero _ written, mul_zero]

private lemma memberSequence_zero_on_agreement (input : Input N) (batch : Fin count)
    (length : Nat) (indices : Fin length → Fin membersPerBatch)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (zero : ∀ stored, batchSourceAgreement base N count input batch stored → weight stored = 0)
    (stored : Store (Recycling.ClassicalFrame.context base N count))
    (agrees : batchSourceAgreement base N count input batch stored) :
    Circuit.forRangeReferenceKernel length
      (fun index => memberParentReferenceKernel base N count batch (indices index)) weight stored =
        0 := by
  induction length generalizing stored with
  | zero => exact zero stored agrees
  | succ length ih =>
      apply memberKernel_zero_on_agreement base N count input batch (indices 0) _ _ stored agrees
      intro before condition
      exact ih (fun index => indices index.succ) before condition

/-- The actual member bank preserves the native source condition on every positive record. -/
lemma rsaMeasuredParent_members_admitted (input : Input N) [NeZero (modulusWord N).toNat]
    (batch : Fin count) (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (admitted : ∀ record, 0 < (state.block record).mass →
      batchSourceAgreement base N count input batch
        (parentStoreAt base noQuantum N count record.1)) :
    ∀ record, 0 < (((members base noQuantum N input count batch).execute
      environment Reference state).block record).mass →
      batchSourceAgreement base N count input batch
        (parentStoreAt base noQuantum N count record.1) := by
  apply ExecutionState.supported_of_reference_zero
  intro left right
  let bad : Store (Recycling.ClassicalFrame.context base N count) → ℂ :=
    fun stored => if batchSourceAgreement base N count input batch stored then 0 else 1
  have empty : ∀ stored, batchSourceAgreement base N count input batch stored → bad stored = 0 :=
    fun _ condition => if_pos condition
  refine (rsaMeasuredParent_members_parent_referenceFiberSum base noQuantum N input count batch
    environment state seeded bad left right).trans ?_
  refine (ExecutionState.referenceFiberSum_congr_on_positive state
    (fun record _ => membersParentReferenceKernel base N count batch bad
      (parentStoreAt base noQuantum N count record.1)) (fun _ _ => 0) ?_ left right).trans ?_
  · intro record positive _basis
    exact memberSequence_zero_on_agreement base N count input batch membersPerBatch id bad empty
      (parentStoreAt base noQuantum N count record.1) (admitted record positive)
  · simp only [ExecutionState.referenceFiberSum, zero_mul, Finset.sum_const_zero]

end

end QuantumAlg.Factoring.RSA.Measured.Program
