/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Source
import all QuantumAlg.Core.Execution.Reference.Admission
import all QuantumAlg.Components.Classical.Model.BitWord.Random.Indexed
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Source agreement is established by the actual native source execution

The actual stored source bits name the same finite random draw used by the
paid parameter program. Every positive actual output record therefore
satisfies the recovery's existing initial condition. This is an internal
execution consequence for arbitrary original Store/reference inputs
[EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Mathematical observation of the actual native source cell in its original bit convention. -/
def sourceStoredSample {ctx : RuntimeCtx .quantum} {N : Nat}
    (sample : CInputRef ctx (.bits (residueSamplingBits N))) (stored : Store ctx) :
    Fin (2 ^ residueSamplingBits N) :=
  BitWord.Random.sampleEquiv (residueSamplingBits N) (stored.read sample)

/-- The real complete parameter agrees with the same source draw retained in the caller cell. -/
def SourceAgreement {ctx : RuntimeCtx .quantum} {N : Nat} (input : Input N)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (parameter : CInputRef ctx (ParameterShape N)) (stored : Store ctx) : Prop :=
  stored.read parameter = parameterValue input (sourceStoredSample sample stored)

/-- Writes outside both real source operands preserve their complete source agreement. -/
lemma rsaMeasuredParent_sourceAgreement_write {ctx : RuntimeCtx .quantum} {N : Nat}
    (input : Input N) (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (parameter : CInputRef ctx (ParameterShape N)) {shape : CShape}
    (result : CWriteRef ctx shape) (value : shape.Value) (stored : Store ctx)
    (separateSample : result.key ∉ sample.storageKeys)
    (separateParameter : result.key ∉ parameter.storageKeys)
    (agrees : SourceAgreement input sample parameter stored) :
    SourceAgreement input sample parameter (stored.write result value) := by
  unfold SourceAgreement sourceStoredSample at agrees ⊢
  rw [Store.read_write_of_not_mem_storageKeys stored result value parameter separateParameter,
    Store.read_write_of_not_mem_storageKeys stored result value sample separateSample]
  exact agrees

/-- The actual paid source writes both its same finite draw and that draw's complete parameter. -/
lemma rsaMeasuredParent_sourceStore_agreement {ctx : RuntimeCtx .quantum} {N : Nat}
    (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
    (parameter : CWriteRef ctx (ParameterShape N)) (input : Input N)
    (separate : parameter.key ≠ sample.key) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    SourceAgreement input (FirstAccepted.cellRead sample) (FirstAccepted.cellRead parameter)
      (sourceStore N sample parameter before value) := by
  have stored := rsaMeasuredParent_sourceStore_sample N sample parameter input before value separate
  have decoded : sourceStoredSample (FirstAccepted.cellRead sample)
      (sourceStore N sample parameter before value) = value := by
    unfold sourceStoredSample
    rw [stored, ← ShorStyle.Canonical.Sampler.PackedSample.decoded_sample]
    exact Equiv.apply_symm_apply _ _
  exact (rsaMeasuredParent_sourceStore_parameter N sample parameter input before value).trans
    (congrArg (parameterValue input) decoded.symm)

/-- Every positive native-source record has agreement, including arbitrary old caller contents. -/
lemma rsaMeasuredParent_source_parent_admitted {outer inner : RuntimeCtx .quantum} {N : Nat}
    (transport : ClassicalWorkspace.Transport outer inner)
    (sample : CWriteRef outer (.bits (residueSamplingBits N)))
    (parameter : CWriteRef outer (ParameterShape N)) (input : Input N)
    (separate : parameter.key ≠ sample.key) (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (MeasuredRSAModel.HiddenState × History)) :
    ∀ record, 0 <
      (((source N (transport.liftWrite sample) (transport.liftWrite parameter)).execute
        environment Reference state).block record).mass →
      SourceAgreement input (FirstAccepted.cellRead sample) (FirstAccepted.cellRead parameter)
        (transport.restrict record.1) := by
  apply ExecutionState.supported_of_reference_zero
  intro left right
  have actual := rsaMeasuredParent_source_parent_referenceFiberSum (environment := environment)
    N transport sample parameter input state
    (fun stored => if SourceAgreement input (FirstAccepted.cellRead sample)
      (FirstAccepted.cellRead parameter) stored then 0 else 1) left right
  refine actual.trans ?_
  have weights :
      (fun entry : Store inner × (MeasuredRSAModel.HiddenState × History) =>
        fun _basis : inner.register.Index =>
          ∑ value : Fin (2 ^ residueSamplingBits N),
            (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
              (if SourceAgreement input (FirstAccepted.cellRead sample)
                (FirstAccepted.cellRead parameter)
                (sourceStore N sample parameter (transport.restrict entry.1) value)
                then 0 else 1)) = (fun _ _ => 0) := by
    funext entry _basis
    simp only [rsaMeasuredParent_sourceStore_agreement sample parameter input separate,
      if_true, mul_zero, Finset.sum_const_zero]
  rw [weights]
  simp only [ExecutionState.referenceFiberSum, zero_mul, Finset.sum_const_zero]

end

end QuantumAlg.Factoring.RSA.Measured.Program
