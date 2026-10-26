/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Born
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Parent
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Terminal
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit

/-!
# Actual RSA member kernel at the original complete terminal labels

Every complete parent Store retains its actual stored parameter. The real
member, native packing and full reset/reload have the original terminal Born
law. Reset establishes the next seed internally even after the final member
[EH17, source.tex:878-966; G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open ShortDLP.CompiledMAU.Recycling.Measured
open ShortDLP.CompiledMAU.Recycling (resultBits)
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The entire original classical batch frame is retained below the measured arithmetic bank. -/
def parentStoreAt (count : Nat) (stored : Store (readyContext base noQuantum N count)) :
    Store (Recycling.ClassicalFrame.context base N count) :=
  parentStore (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) stored

/-- The physical bank seed is established by actual initial loading and every complete round. -/
def memberSeed (count : Nat) : (readyContext base noQuantum N count).register.Index :=
  preparedSeed (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (modulusWord N).toNat

/-- Original terminal Born probabilities transport the real packed destination in the parent. -/
def memberParentReferenceKernel (count : Nat) (batch : Fin count) (index : Fin membersPerBatch)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) : ℂ :=
  ∑ terminal : Fin (measurementBits N) → Bool,
    ((selectedOutcomePMF
      (stored.read
        (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch)))
      terminal).toReal : ℂ) *
        weight (stored.write (Recycling.ClassicalFrame.packedRef base N count batch index)
          (.bits terminal))

/-- The exact two-stream bijection reindexes the same real parent write by original terminals. -/
lemma rsaMeasuredParent_member_kernel_terminal (input : Input N)
    [NeZero (modulusWord N).toNat] (count : Nat) (batch : Fin count)
    (index : Fin membersPerBatch)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    Round.parentReferenceKernel (Recycling.ClassicalFrame.context base N count)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
      (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))
      (modulusWord N) (parameterGenerator N) (parameterTargetWord N)
      (Recycling.ClassicalFrame.packedRef base N count batch index)
      weight (parentStoreAt base noQuantum N count stored) =
        memberParentReferenceKernel base N count batch index weight
          (parentStoreAt base noQuantum N count stored) := by
  have reindex :=
    (measuredMemberTerminalEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).sum_comp
      (fun terminal =>
        ((selectedOutcomePMF
          ((parentStoreAt base noQuantum N count stored).read
            (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch)))
          terminal).toReal : ℂ) *
            weight ((parentStoreAt base noQuantum N count stored).write
              (Recycling.ClassicalFrame.packedRef base N count batch index) (.bits terminal)))
  refine Eq.trans ?_ reindex
  unfold Round.parentReferenceKernel
  apply Finset.sum_congr rfl
  intro readout _
  have born := measuredRSA_memberBornWeight input
    ((parentStoreAt base noQuantum N count stored).read
      (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))) readout
  have packed := measuredPackedReadout_terminal (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) stored readout
  let destination : CWriteRef (Recycling.ClassicalFrame.context base N count)
      (.bits (resultBits (shortLogBits N) (tradeoffBits N))) :=
    Recycling.ClassicalFrame.packedRef base N count batch index
  exact (congrArg₂
    (fun (outcome : CShape.Value (.bits (resultBits (shortLogBits N) (tradeoffBits N))))
      (probability : ℝ) =>
      weight ((parentStoreAt base noQuantum N count stored).write destination outcome) *
        (probability : ℂ)) packed born).trans (mul_comm _ _)

/-- The actual complete member establishes its successor seed without an incoming promise. -/
lemma rsaMeasuredParent_member_seeded (input : Input N) (count : Nat) (batch : Fin count)
    (index : Fin membersPerBatch) (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History)) :
    BasisSeeded.Holds (memberSeed base noQuantum N count)
      ((member base noQuantum N input count batch index).execute environment Reference state) :=
  Round.measuredRound_seeded (environment := environment)
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (bankWrite base noQuantum N count
      (Recycling.ClassicalFrame.parameterRef base N count batch)))
    (measuredRSA_arithmeticBits_atLeastTwo input) (modulusWord N)
    (parameterGenerator N) (parameterTargetWord N)
    (bankWrite base noQuantum N count (Recycling.ClassicalFrame.packedRef base N count batch index))
    state

/-- Actual fresh measured output propagates every complete parent/reference observation. -/
lemma rsaMeasuredParent_member_parent_referenceFiberSum (input : Input N)
    [NeZero (modulusWord N).toNat] (count : Nat) (batch : Fin count)
    (index : Fin membersPerBatch) (environment : MeasuredRSAModel.Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext base noQuantum N count) Reference
      (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds (memberSeed base noQuantum N count) state)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((member base noQuantum N input count batch index).execute environment Reference state)
      (fun entry _ => weight (parentStoreAt base noQuantum N count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => memberParentReferenceKernel base N count batch index weight
          (parentStoreAt base noQuantum N count entry.1)) left right := by
  have positive : 0 < (modulusWord N).toNat := by
    rw [measuredRSA_modulusWord_toNat]
    exact Nat.zero_lt_of_lt input.modulus_gt_one
  refine (Round.measuredRound_parent_referenceFiberSum
    (Recycling.ClassicalFrame.context base N count)
    (Recycling.ClassicalFrame.frameNoQuantum base noQuantum N count)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))
    (modulusWord N) (measuredRSA_arithmeticBits_atLeastTwo input)
    (parameterGenerator N) (parameterTargetWord N) positive
    (Recycling.ClassicalFrame.packedRef base N count batch index)
    environment Reference state seeded weight left right).trans ?_
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
  funext entry _basis
  exact rsaMeasuredParent_member_kernel_terminal base noQuantum N input count batch index
    weight entry.1

end

end QuantumAlg.Factoring.RSA.Measured.Program
