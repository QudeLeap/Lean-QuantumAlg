/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program.Members
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Util.PMF.VectorMass
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Original conditional independent-member law of the actual parent kernels

Every paid measured member writes one distinct original parent destination.
Those writes preserve the actual source parameter and all other terminal
cells. Chronological composition therefore has the original fixed-source
independent terminal law [EH17, source.tex:878-966].
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program.Probability

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

/-- Original complete terminal labels at the public source widths. -/
abbrev Terminal (N : Nat) := Fin (measurementBits N) → Bool

variable (base : RuntimeCtx .quantum) (N count : Nat)

/-- The complete original parameter retained in its real parent cell. -/
def parameterRead (batch : Fin count)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    (ParameterShape N).Value :=
  stored.read (FirstAccepted.cellRead (Recycling.ClassicalFrame.parameterRef base N count batch))

/-- One actual paid member's parent update, in the unchanged original terminal coordinates. -/
def updateMember (batch : Fin count) (index : Fin membersPerBatch) (terminal : Terminal N)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    Store (Recycling.ClassicalFrame.context base N count) :=
  stored.write (Recycling.ClassicalFrame.packedRef base N count batch index) (.bits terminal)

/-- A paid terminal write preserves every original source parameter. -/
lemma rsaMeasuredProbability_update_parameter (batch previous : Fin count)
    (index : Fin membersPerBatch) (terminal : Terminal N)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    parameterRead base N count previous (updateMember base N count batch index terminal stored) =
      parameterRead base N count previous stored :=
  Store.read_write_other stored (Recycling.ClassicalFrame.packedRef base N count batch index)
    (Recycling.ClassicalFrame.parameterRef base N count previous).toCStorageRef (.bits terminal)
    (Recycling.ClassicalFrame.rsaRecyclingFrame_packed_parameter_separate
      base N count batch previous index)

/-- The real chronological parent writes follow the same increasing member order. -/
def memberStores (batch : Fin count) : (length : Nat) → (Fin length → Fin membersPerBatch) →
    List.Vector (Terminal N) length → Store (Recycling.ClassicalFrame.context base N count) →
      Store (Recycling.ClassicalFrame.context base N count)
  | 0, _, _, stored => stored
  | length + 1, indices, values, stored =>
      memberStores batch length (fun index => indices index.succ) values.tail
        (updateMember base N count batch (indices 0) values.head stored)

/-- All real terminal destinations preserve the original full stored source parameter. -/
lemma rsaMeasuredProbability_memberStores_parameter (batch previous : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch) (values : List.Vector (Terminal N) length)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    parameterRead base N count previous
      (memberStores base N count batch length indices values stored) =
        parameterRead base N count previous stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) values.tail _).trans
        (rsaMeasuredProbability_update_parameter base N count batch previous (indices 0)
          values.head stored)

/-- Every original parent observation has the source's unchanged independent terminal moment. -/
lemma rsaMeasuredProbability_memberSequence_iid (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    Circuit.forRangeReferenceKernel length
        (fun index => memberParentReferenceKernel base N count batch (indices index))
        weight stored =
      ∑ values : List.Vector (Terminal N) length,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterRead base N count batch stored)) length
          values).toReal : ℂ) *
            weight (memberStores base N count batch length indices values stored) := by
  induction length generalizing stored with
  | zero =>
      simp only [Circuit.forRangeReferenceKernel, memberStores,
        PMF.independentReplicateVector, PMF.pure_apply, apply_ite, ENNReal.toReal_one,
        ENNReal.toReal_zero, Complex.ofReal_one, Complex.ofReal_zero,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ length ih =>
      rw [Circuit.forRangeReferenceKernel, PMF.independentReplicateVector_weighted_cons]
      rw [memberParentReferenceKernel]
      apply Finset.sum_congr rfl
      intro terminal _
      apply congrArg (fun value : ℂ =>
        ((selectedOutcomePMF (parameterRead base N count batch stored) terminal).toReal : ℂ) *
          value)
      have tail := ih (fun index => indices index.succ)
        (updateMember base N count batch (indices 0) terminal stored)
      refine (show Circuit.forRangeReferenceKernel length
          (fun index => memberParentReferenceKernel base N count batch (indices index.succ))
          weight (stored.write (Recycling.ClassicalFrame.packedRef base N count batch (indices 0))
            (.bits terminal)) =
        Circuit.forRangeReferenceKernel length
          (fun index => memberParentReferenceKernel base N count batch (indices index.succ))
          weight (updateMember base N count batch (indices 0) terminal stored) from rfl).trans ?_
      refine tail.trans ?_
      apply Finset.sum_congr rfl
      intro values _
      have parameterSame := rsaMeasuredProbability_update_parameter base N count batch batch
        (indices 0) terminal stored
      exact congrArg₂ (fun coefficient : ℂ => fun finalStore => coefficient * weight finalStore)
        (congrArg (fun parameter => ((PMF.independentReplicateVector
          (selectedOutcomePMF parameter) length values).toReal : ℂ)) parameterSame)
        (show memberStores base N count batch length (fun index => indices index.succ) values
            (updateMember base N count batch (indices 0) terminal stored) =
          memberStores base N count batch (length + 1) indices
            (List.Vector.cons terminal values) stored from rfl)


/-- The entire actual configured-member parent kernel has the same complete iid expansion. -/
lemma rsaMeasuredProbability_membersKernel_iid (batch : Fin count)
    (weight : Store (Recycling.ClassicalFrame.context base N count) → ℂ)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    membersParentReferenceKernel base N count batch weight stored =
      ∑ values : List.Vector (Terminal N) membersPerBatch,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterRead base N count batch stored)) membersPerBatch
            values).toReal : ℂ) *
          weight (memberStores base N count batch membersPerBatch id values stored) :=
  rsaMeasuredProbability_memberSequence_iid base N count batch membersPerBatch id weight stored

/-- The true packed parent input read by complete native recovery. -/
def packedRead (batch : Fin count) (index : Fin membersPerBatch)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    CShape.Value (.bits (measurementBits N)) :=
  stored.read (FirstAccepted.cellRead (Recycling.ClassicalFrame.packedRef base N count batch index))

private lemma rsaMeasuredProbability_update_read_same (batch : Fin count)
    (index : Fin membersPerBatch) (terminal : Terminal N)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    packedRead base N count batch index (updateMember base N count batch index terminal stored) =
      .bits terminal :=
  Store.read_write_same stored (Recycling.ClassicalFrame.packedRef base N count batch index) _

private lemma rsaMeasuredProbability_update_read_other (batch : Fin count)
    (index other : Fin membersPerBatch) (different : index ≠ other) (terminal : Terminal N)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    packedRead base N count batch other (updateMember base N count batch index terminal stored) =
      packedRead base N count batch other stored := by
  apply Store.read_write_other
  intro same
  have addresses : (batch, index) = (batch, other) :=
    Recycling.ClassicalFrame.rsaRecyclingFrame_packedRef_distinct base N count same
  exact different (congrArg Prod.snd addresses)

private lemma rsaMeasuredProbability_memberStores_read_other (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch) (other : Fin membersPerBatch)
    (outside : ∀ index, indices index ≠ other) (values : List.Vector (Terminal N) length)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) :
    packedRead base N count batch other
      (memberStores base N count batch length indices values stored) =
      packedRead base N count batch other stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) (fun index => outside index.succ)
        values.tail _).trans (rsaMeasuredProbability_update_read_other base N count batch
          (indices 0) other (outside 0) values.head stored)

/-- Every distinct actual destination contains its corresponding original sampled terminal. -/
lemma rsaMeasuredProbability_memberStores_read (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin membersPerBatch) (injective : Function.Injective indices)
    (values : List.Vector (Terminal N) length)
    (stored : Store (Recycling.ClassicalFrame.context base N count)) (index : Fin length) :
    packedRead base N count batch (indices index)
      (memberStores base N count batch length indices values stored) =
        .bits (values.get index) := by
  induction length generalizing stored with
  | zero => exact Fin.elim0 index
  | succ length ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simpa only [memberStores, List.Vector.get_zero] using
          (rsaMeasuredProbability_memberStores_read_other base N count batch length
            (fun index => indices index.succ) (indices 0)
            (fun index same => Fin.succ_ne_zero index (injective same)) values.tail _).trans
              (rsaMeasuredProbability_update_read_same base N count batch (indices 0)
                values.head stored)
      · simpa only [memberStores, List.Vector.get_tail_succ] using
          ih (fun index => indices index.succ)
            (fun _ _ same => Fin.succ_injective _ (injective same)) values.tail
            (updateMember base N count batch (indices 0) values.head stored) index

end

end QuantumAlg.Factoring.RSA.Measured.Program.Probability
