/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members.Admission
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Observation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Seed
import all QuantumAlg.Core.Execution.Reference.Admission

/-!
# Actual first source and preparation establish the complete first-batch conditions

The first native source runs before the sole quantum allocation. Its own
actual writes establish source agreement. Real bank preparation retains that
entire parent condition and supplies the complete physical seed for arbitrary
original Store/reference inputs [EH17, source.tex:878-966; G25, main.tex:199-295].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Every actual first-source record satisfies the original recovery source condition. -/
lemma rsaMeasuredParent_firstSource_admitted (input : Input N) (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Recycling.ClassicalFrame.context base N (laterCount + 1)) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    ∀ record, 0 < (((firstSource base N laterCount).execute environment Reference state).block
      record).mass → batchSourceAgreement base N (laterCount + 1) input 0 record.1 := by
  intro record positive
  have actual := rsaMeasuredParent_source_parent_admitted
    (ClassicalWorkspace.Transport.id (Recycling.ClassicalFrame.context base N (laterCount + 1)))
    (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0) input
    (Recycling.ClassicalFrame.rsaRecyclingFrame_sample_parameter_separate
      base N (laterCount + 1) 0 0).symm environment state record positive
  simpa only [ClassicalWorkspace.Transport.workspaceTransport_restrict_id, batchSourceAgreement]
    using actual

/-- Real bank preparation preserves the actual supported source condition in the entire parent. -/
lemma rsaMeasuredParent_prepare_source_admitted (input : Input N) (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History]
    (state : State (Recycling.ClassicalFrame.context base N (laterCount + 1)) Reference
      (MeasuredRSAModel.HiddenState × History))
    (admitted : ∀ record, 0 < (state.block record).mass →
      batchSourceAgreement base N (laterCount + 1) input 0 record.1) :
    ∀ record, 0 <
      (((prepare (Recycling.ClassicalFrame.context base N (laterCount + 1))
        (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat).execute
          environment Reference state).block record).mass →
      batchSourceAgreement base N (laterCount + 1) input 0
        (parentStoreAt base noQuantum N (laterCount + 1) record.1) := by
  apply ExecutionState.supported_of_reference_zero
  intro left right
  refine (PreparationObservation.prepare_referenceFiberSum_parent (environment := environment)
    (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat state
    (fun stored => if batchSourceAgreement base N (laterCount + 1) input 0 stored then 0 else 1)
    left right).trans ?_
  exact ExecutionState.referenceFiberSum_bad_eq_zero state
    (fun record => batchSourceAgreement base N (laterCount + 1) input 0 record.1)
    admitted left right

/-- Actual complete allocation and literal loading establish the first physical bank seed. -/
lemma rsaMeasuredParent_prepare_seeded (count : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State (Recycling.ClassicalFrame.context base N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      (((prepare (Recycling.ClassicalFrame.context base N count)
        (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat).execute
          environment Reference state)) :=
  measuredPrepare_seeded (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) environment (modulusWord N).toNat state

end

end QuantumAlg.Factoring.RSA.Measured.Program
