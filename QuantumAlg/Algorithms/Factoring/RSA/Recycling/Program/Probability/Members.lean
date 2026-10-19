/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Probability.Member
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Reference
import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program.Projection
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Core.Execution.Reference.Kernel
import all QuantumAlg.Util.PMF.VectorMass

/-!
# Sixteen actual chronological members have the fixed-source iid law

Induction follows the actual backward kernel and retains the complete Store
produced by every paid member. Parameter preservation makes the single-member
Born PMF identical at each step. The slot projection then identifies all
sixteen terminal cells, independently of their arbitrary initial contents.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program.Probability

noncomputable section

open Execution ClassicalRoutines EkeraHastadStyle.Canonical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- Compose exactly the actual Store updates in their original increasing execution order. -/
def memberStores (batch : Fin count) : (length : Nat) → (Fin length → Fin 16) →
    List.Vector (Terminal N) length → Store (readyContext base noQuantum N count) →
      Store (readyContext base noQuantum N count)
  | 0, _, _, stored => stored
  | length + 1, indices, values, stored =>
      memberStores batch length (fun index => indices index.succ) values.tail
        (updateMember base noQuantum N count batch (indices 0) values.head stored)

/-- Actual chronological members preserve every source parameter. -/
lemma memberStores_parameter (batch previous : Fin count) (length : Nat)
    (indices : Fin length → Fin 16) (values : List.Vector (Terminal N) length)
    (stored : Store (readyContext base noQuantum N count)) :
    parameterRead base noQuantum N count previous
        (memberStores base noQuantum N count batch length indices values stored) =
      parameterRead base noQuantum N count previous stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) values.tail _).trans
        (updateMember_parameter base noQuantum N count batch previous (indices 0)
          values.head stored)

/-- Every complete-Store observation has the independent terminal law of the stored source. -/
lemma memberSequence_iid (input : Input N) (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin 16)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    Circuit.forRangeReferenceKernel length
        (fun index => memberReferenceKernel base noQuantum N count batch (indices index))
        weight stored =
      ∑ values : List.Vector (Terminal N) length,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterRead base noQuantum N count batch stored)) length
            values).toReal : ℂ) *
          weight (memberStores base noQuantum N count batch length indices values stored) := by
  induction length generalizing stored with
  | zero =>
      simp only [Circuit.forRangeReferenceKernel, memberStores,
        PMF.independentReplicateVector, PMF.pure_apply, apply_ite, ENNReal.toReal_one,
        ENNReal.toReal_zero, Complex.ofReal_one, Complex.ofReal_zero,
        ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ length ih =>
      rw [Circuit.forRangeReferenceKernel,
        memberReferenceKernel_terminal base noQuantum N count input,
        PMF.independentReplicateVector_weighted_cons]
      apply Finset.sum_congr rfl
      intro terminal _
      apply congrArg (fun value : ℂ =>
        ((selectedOutcomePMF (parameterRead base noQuantum N count batch stored)
          terminal).toReal : ℂ) * value)
      have tail := ih (fun index => indices index.succ)
        (updateMember base noQuantum N count batch (indices 0) terminal stored)
      simpa only [updateMember_parameter, memberStores,
        List.Vector.head_cons, List.Vector.tail_cons] using tail

/-- The actual complete sixteen-member kernel has the same full-Store iid expansion. -/
lemma membersReferenceKernel_iid (input : Input N) (batch : Fin count)
    (weight : Store (readyContext base noQuantum N count) → ℂ)
    (stored : Store (readyContext base noQuantum N count)) :
    membersReferenceKernel base noQuantum N count batch weight stored =
      ∑ values : List.Vector (Terminal N) 16,
        ((PMF.independentReplicateVector
          (selectedOutcomePMF (parameterRead base noQuantum N count batch stored)) 16
            values).toReal : ℂ) *
          weight (memberStores base noQuantum N count batch 16 id values stored) :=
  memberSequence_iid base noQuantum N count input batch 16 id weight stored

/-- The structural read used by the actual recovery for one packed terminal. -/
def packedRead (batch : Fin count) (index : Fin 16)
    (stored : Store (readyContext base noQuantum N count)) :
    CShape.Value (.bits (measurementBits N)) :=
  stored.read (terminals base noQuantum N count batch index)

private lemma updateMember_read_same (batch : Fin count) (index : Fin 16)
    (terminal : Terminal N) (stored : Store (readyContext base noQuantum N count)) :
    packedRead base noQuantum N count batch index
      (updateMember base noQuantum N count batch index terminal stored) = .bits terminal := by
  have actual := rsaRecyclingParent_packedStore_output base noQuantum N count batch index
    stored ((terminalEquiv N).symm terminal)
  exact actual.trans (congrArg CShape.Value.bits ((terminalEquiv N).apply_symm_apply terminal))

private lemma updateMember_read_other (batch : Fin count) (index other : Fin 16)
    (different : index ≠ other) (terminal : Terminal N)
    (stored : Store (readyContext base noQuantum N count)) :
    packedRead base noQuantum N count batch other
        (updateMember base noQuantum N count batch index terminal stored) =
      packedRead base noQuantum N count batch other stored :=
  rsaRecyclingParent_packedStore_otherPacked base noQuantum N count batch batch index other
    (fun same => different (congrArg Prod.snd same)) stored _

private lemma memberStores_read_other (batch : Fin count) (length : Nat)
    (indices : Fin length → Fin 16) (other : Fin 16)
    (outside : ∀ index, indices index ≠ other) (values : List.Vector (Terminal N) length)
    (stored : Store (readyContext base noQuantum N count)) :
    packedRead base noQuantum N count batch other
        (memberStores base noQuantum N count batch length indices values stored) =
      packedRead base noQuantum N count batch other stored := by
  induction length generalizing stored with
  | zero => rfl
  | succ length ih =>
      exact (ih (fun index => indices index.succ) (fun index => outside index.succ)
        values.tail _).trans (updateMember_read_other base noQuantum N count batch
          (indices 0) other (outside 0) values.head stored)

/-- Distinct chronological destinations contain the corresponding actual sampled terminal. -/
lemma memberStores_read (batch : Fin count) (length : Nat) (indices : Fin length → Fin 16)
    (injective : Function.Injective indices) (values : List.Vector (Terminal N) length)
    (stored : Store (readyContext base noQuantum N count)) (index : Fin length) :
    packedRead base noQuantum N count batch (indices index)
      (memberStores base noQuantum N count batch length indices values stored) =
        .bits (values.get index) := by
  induction length generalizing stored with
  | zero => exact Fin.elim0 index
  | succ length ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simpa only [memberStores, List.Vector.get_zero] using
          (memberStores_read_other base noQuantum N count batch length
          (fun index => indices index.succ) (indices 0)
          (fun index same => Fin.succ_ne_zero index (injective same)) values.tail _).trans
            (updateMember_read_same base noQuantum N count batch (indices 0) values.head stored)
      · simpa only [memberStores, List.Vector.get_tail_succ] using
          ih (fun index => indices index.succ)
            (fun _ _ same => Fin.succ_injective _ (injective same)) values.tail
            (updateMember base noQuantum N count batch (indices 0) values.head stored) index

end

end QuantumAlg.Factoring.RSA.Recycling.Program.Probability
