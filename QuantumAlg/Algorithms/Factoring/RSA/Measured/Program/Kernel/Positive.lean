/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Kernel

/-!
# Complete parent/reference kernel of the actual positive measured RSA program

The actual classical allocator, first native source, sole quantum allocation,
all complete measured batches and final native selector form one execution.
Both source agreement and the physical seed are established internally. No
initial scratch or seed promise restricts the original caller/reference input
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured
open scoped BigOperators

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- Exact native source kernel on its unchanged complete parent frame. -/
def sourceParentReferenceKernel (count : Nat) (batch : Fin count)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) : ℂ :=
  ∑ value : Fin (2 ^ residueSamplingBits N),
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
      weight (sourceStore N (Recycling.ClassicalFrame.sampleRef base N count batch)
        (Recycling.ClassicalFrame.parameterRef base N count batch) stored value)

/-- The original source draw acts on the actual initialized complete classical parent frame. -/
def positiveParentReferenceKernel (laterCount : Nat)
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ)
    (original : Store base) : ℂ :=
  sourceParentReferenceKernel base N (laterCount + 1) 0
    (tailParentReferenceKernel base N laterCount weight)
    (Recycling.ClassicalFrame.pushStore base N (laterCount + 1) original)

/-- The sole actual positive program propagates every parent/reference observation from input. -/
lemma rsaMeasuredParent_positiveCode_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (laterCount : Nat)
    (environment : MeasuredRSAModel.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State base Reference (MeasuredRSAModel.HiddenState × History))
    (weight : Store (Recycling.ClassicalFrame.context base N (laterCount + 1)) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((positiveCode base noQuantum N input laterCount).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N (laterCount + 1) entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => positiveParentReferenceKernel base N laterCount weight entry.1)
        left right := by
  let allocated : Circuit MeasuredRSAModel base
      (Recycling.ClassicalFrame.context base N (laterCount + 1)) :=
    Recycling.ClassicalFrame.allocate base N (laterCount + 1)
  let drawn : Circuit MeasuredRSAModel
      (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.context base N (laterCount + 1)) :=
    firstSource base N laterCount
  let prepared : Circuit MeasuredRSAModel
      (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    prepare (Recycling.ClassicalFrame.context base N (laterCount + 1))
      (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat
  let tail : Circuit MeasuredRSAModel (readyContext base noQuantum N (laterCount + 1))
      (readyContext base noQuantum N (laterCount + 1)) :=
    (batchBody base noQuantum N input (laterCount + 1) 0).seq
      ((Circuit.forRange laterCount fun index =>
        nextBatch base noQuantum N input (laterCount + 1) index.succ).seq
          (select base noQuantum N (laterCount + 1)))
  refine (Circuit.referenceFiberSum_execute_seq allocated (drawn.seq (prepared.seq tail))
    environment state
    (fun stored => weight (parentStoreAt base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq drawn (prepared.seq tail) environment
    (allocated.execute environment Reference state)
    (fun stored => weight (parentStoreAt base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  refine (Circuit.referenceFiberSum_execute_seq prepared tail environment
    (drawn.execute environment Reference (allocated.execute environment Reference state))
    (fun stored => weight (parentStoreAt base noQuantum N (laterCount + 1) stored))
    left right).trans ?_
  refine (rsaMeasuredParent_tail_parent_referenceFiberSum base noQuantum N input laterCount
    environment (prepared.execute environment Reference
      (drawn.execute environment Reference (allocated.execute environment Reference state)))
    (rsaMeasuredParent_prepare_seeded base noQuantum N (laterCount + 1) environment _)
    (rsaMeasuredParent_prepare_source_admitted base noQuantum N input laterCount environment _
      (rsaMeasuredParent_firstSource_admitted base N input laterCount environment
        (allocated.execute environment Reference state))) weight left right).trans ?_
  refine (PreparationObservation.prepare_referenceFiberSum_parent (environment := environment)
    (Recycling.ClassicalFrame.context base N (laterCount + 1))
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N (laterCount + 1))
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat
    (drawn.execute environment Reference (allocated.execute environment Reference state))
    (tailParentReferenceKernel base N laterCount weight) left right).trans ?_
  refine (rsaMeasuredParent_source_referenceFiberSum (environment := environment) N
    (Recycling.ClassicalFrame.sampleRef base N (laterCount + 1) 0)
    (Recycling.ClassicalFrame.parameterRef base N (laterCount + 1) 0)
    (allocated.execute environment Reference state)
    (tailParentReferenceKernel base N laterCount weight) left right).trans ?_
  have allocatedEquation :=
    Recycling.ClassicalFrame.rsaRecyclingFrame_allocate_referenceFiberSum
      (environment := environment) base N (laterCount + 1) state
      (sourceParentReferenceKernel base N (laterCount + 1) 0
        (tailParentReferenceKernel base N laterCount weight)) left right
  exact allocatedEquation

end

end QuantumAlg.Factoring.RSA.Measured.Program
