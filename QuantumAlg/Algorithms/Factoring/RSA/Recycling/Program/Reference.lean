/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.ClassicalFrame.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Reference
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Seeded.Born
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Reference.Kernel

/-!
# Complete stored-reference kernels of the actual sixteen RSA members

Each native member reads the parameter in the real batch cell and performs
the existing measured arithmetic, paid packing, bank reset and reload. Its
backward kernel uses the original compiled Born mass at the actual decoded
frequencies and the complete resulting Store. Composing these kernels follows
the real increasing member indices. It preserves incoming Store correlations,
write collisions and both external-reference coordinates.

The seed required by the first member is supplied by actual preparation; every
complete member restores it for its successor. No independent product law or
old dynamically retained executor is used. The separate complete partner
instrument remains available before the physical reset and partial trace.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The actual allocation and every terminal restart establish this same physical bank seed. -/
def memberSeed (count : Nat) : (readyContext base noQuantum N count).register.Index :=
  ShortDLP.CompiledMAU.Recycling.Reload.seed (ClassicalFrame.context base N count)
    (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N

/-- The unchanged compiled source mass uses the parameter read from the actual complete Store. -/
def memberBornWeight (count : Nat) (batch : Fin count)
    (original : Store (readyContext base noQuantum N count))
    (outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N)) : ℝ :=
  let parameter := original.read (FirstAccepted.cellRead
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.parameterRef base N count batch)))
  let frequency := ShortDLP.CompiledMAU.Recycling.PackedReference.frequencies
    (shortLogBits N) (tradeoffBits N) outcome
  ((ShortDLP.measurement (registerParameters
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).outcomePMF
      (evolvedState (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
        (parameterUnit parameter) (parameterTarget parameter))
      (ShortDLP.CompiledMAU.Recycling.SeededBorn.sourceOutcome
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N) frequency.1 frequency.2)).toReal

/-- One real member transports a complete-store observation through its paid packed result. -/
def memberReferenceKernel (count : Nat) (batch : Fin count) (index : Fin 16)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (original : Store (readyContext base noQuantum N count)) : ℂ :=
  ∑ outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N),
    weight (ShortDLP.CompiledMAU.Recycling.PackedReference.packedStore
      (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index))
      original outcome) * (memberBornWeight base noQuantum N count batch original outcome : ℂ)

/-- The backward observation follows the exact increasing sixteen-member execution order. -/
def membersReferenceKernel (count : Nat) (batch : Fin count) :
    (Store (readyContext base noQuantum N count) → ℂ) →
      Store (readyContext base noQuantum N count) → ℂ :=
  Circuit.forRangeReferenceKernel 16 (memberReferenceKernel base noQuantum N count batch)

private lemma weighted_reference {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right =
      ∑ original : Store ctx, weight original *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          left right := by
  have grouped :=
    ShortDLP.CompiledMAU.Recycling.PackedReference.weighted_store_reference state weight left right
  refine grouped.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply congrArg (fun value : ℂ => weight original * value)
  symm
  rw [ExecutionState.referenceMarginal, DensityOperator.marginalLeft_matrix]
  rfl

/-- Actual paid reset and reload restore the bank after any incoming state and complete member. -/
lemma rsaRecyclingParent_member_seeded (count : Nat) (batch : Fin count) (index : Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((member base noQuantum N count batch index).execute environment Reference state) :=
  ShortDLP.CompiledMAU.Recycling.Round.code_seeded
    (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch))) N
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.packedRef base N count batch index))
    state

/-- Each actual complete member has the source Born kernel on all stored-reference entries. -/
lemma rsaRecyclingParent_member_referenceFiberSum (input : Input N)
    (count : Nat) (batch : Fin count) (index : Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((member base noQuantum N count batch index).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => memberReferenceKernel base noQuantum N count batch index weight entry.1)
        left right := by
  classical
  let : NeZero N := input.neZero
  let modulus : Fin (2 ^ arithmeticBits N + 1) :=
    ⟨N, Nat.lt_succ_of_lt (modulus_lt_arithmeticCapacity N)⟩
  have actual := ShortDLP.CompiledMAU.Recycling.PackedReference.round_referenceFiberSum
    (environment := environment)
    (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) modulus
    input.modulus_gt_one (modulus_lt_arithmeticCapacity N)
    (FirstAccepted.cellRead (ClassicalFrame.bankWrite noQuantum N count
      (ClassicalFrame.parameterRef base N count batch)))
    (parameterUnit (N := N)) (parameterTarget (N := N))
    (ClassicalFrame.bankWrite noQuantum N count (ClassicalFrame.packedRef base N count batch index))
    state seeded weight left right
  refine actual.trans ?_
  rw [weighted_reference]
  apply Finset.sum_congr rfl
  intro original _
  change (∑ outcome : Bits (tradeoffBits N + shortLogBits N) × Bits (tradeoffBits N),
    weight (ShortDLP.CompiledMAU.Recycling.PackedReference.packedStore
      (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (ClassicalFrame.bankWrite noQuantum N count
        (ClassicalFrame.packedRef base N count batch index))
      original outcome) * (memberBornWeight base noQuantum N count batch original outcome : ℂ) *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          left right) =
    memberReferenceKernel base noQuantum N count batch index weight original *
      (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix left right
  exact (Finset.sum_mul _ _ _).symm

private lemma memberSequence_seeded (count : Nat) (batch : Fin count)
    (length : Nat) (indices : Fin length → Fin 16)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((Circuit.forRange length (fun index =>
        member base noQuantum N count batch (indices index))).execute
          environment Reference state) := by
  induction length generalizing History with
  | zero =>
      rw [Circuit.forRange, Circuit.execute_id_mapClassical]
      exact BasisSeeded.mapStore (memberSeed base noQuantum N count) state seeded id
        (fun entry => (entry.2.1, (entry.2.2, ())))
  | succ length ih =>
      exact BasisSeeded.seq (environment := environment)
        (member base noQuantum N count batch (indices 0))
        (Circuit.forRange length fun index =>
          member base noQuantum N count batch (indices index.succ))
        (memberSeed base noQuantum N count) state
        (ih (fun index => indices index.succ)
          ((member base noQuantum N count batch (indices 0)).execute environment Reference state)
          (rsaRecyclingParent_member_seeded base noQuantum N count batch (indices 0) state))

/-- The actual sixteen-member sequence restores its bank, even for an initially unseeded state. -/
lemma rsaRecyclingParent_members_seeded (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((members base noQuantum N count batch).execute environment Reference state) := by
  exact BasisSeeded.seq (environment := environment) (member base noQuantum N count batch 0)
    (Circuit.forRange 15 fun index => member base noQuantum N count batch index.succ)
    (memberSeed base noQuantum N count) state
    (memberSequence_seeded base noQuantum N count batch 15 Fin.succ
      ((member base noQuantum N count batch 0).execute environment Reference state)
      (rsaRecyclingParent_member_seeded base noQuantum N count batch 0 state))

/-- Actual chronological execution composes all sixteen complete stored-reference kernels. -/
lemma rsaRecyclingParent_members_referenceFiberSum (input : Input N)
    (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((members base noQuantum N count batch).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => membersReferenceKernel base noQuantum N count batch weight entry.1)
        left right := by
  exact Circuit.forRange_referenceFiberSum (environment := environment)
    16 (member base noQuantum N count batch)
    (memberSeed base noQuantum N count) (memberReferenceKernel base noQuantum N count batch)
    (fun index _ _ _ actual =>
      rsaRecyclingParent_member_seeded base noQuantum N count batch index actual)
    (fun index _ _ _ actual supported observation first second =>
      rsaRecyclingParent_member_referenceFiberSum base noQuantum N input count batch index
        actual supported observation first second)
    state seeded weight left right

/-- Every complete Store has the same kernel, including collisions and off-diagonal entries. -/
lemma rsaRecyclingParent_members_store_reference (input : Input N)
    (count : Nat) (batch : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (stored : Store (readyContext base noQuantum N count)) (left right : Reference.Index) :
    (((members base noQuantum N count batch).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).referenceMarginal.matrix left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => membersReferenceKernel base noQuantum N count batch
          (fun result => if result = stored then 1 else 0) entry.1) left right := by
  have actual := rsaRecyclingParent_members_referenceFiberSum (environment := environment)
    base noQuantum N input count batch
    state seeded (fun result => if result = stored then 1 else 0) left right
  have observed := weighted_reference ((members base noQuantum N count batch).execute environment
    Reference state) (fun result => if result = stored then (1 : ℂ) else 0) left right
  have observedEntry :
      ExecutionState.referenceFiberSum
          ((members base noQuantum N count batch).execute environment Reference state)
          (fun entry _ => if entry.1 = stored then (1 : ℂ) else 0) left right =
        (((members base noQuantum N count batch).execute
          environment Reference state).filterClassical
          (fun entry => entry.1 = stored)).referenceMarginal.matrix left right := by
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      using observed
  exact observedEntry.symm.trans actual

/-- Real preparation establishes the only member seed premise for any incoming caller state. -/
lemma rsaRecyclingParent_prepare_members_referenceFiberSum (input : Input N)
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
          (members base noQuantum N count batch)).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum
        ((ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N count)
          (ClassicalFrame.frameNoQuantum base noQuantum N count)
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).execute
            environment Reference state)
        (fun entry _ => membersReferenceKernel base noQuantum N count batch weight entry.1)
        left right := by
  let prepared : Circuit RecycledModel (ClassicalFrame.context base N count)
      (readyContext base noQuantum N count) :=
    ShortDLP.CompiledMAU.Recycling.prepare (ClassicalFrame.context base N count)
      (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
  let repeated : Circuit RecycledModel (readyContext base noQuantum N count)
      (readyContext base noQuantum N count) := members base noQuantum N count batch
  refine (Circuit.referenceFiberSum_execute_seq (environment := environment)
    prepared repeated state weight left right).trans ?_
  exact rsaRecyclingParent_members_referenceFiberSum base noQuantum N input count batch _
    (ShortDLP.CompiledMAU.Recycling.InitialSeed.recyclingPrepare_seeded
      (ClassicalFrame.context base N count) (ClassicalFrame.frameNoQuantum base noQuantum N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N state) weight left right

end

end QuantumAlg.Factoring.RSA.Recycling.Program
