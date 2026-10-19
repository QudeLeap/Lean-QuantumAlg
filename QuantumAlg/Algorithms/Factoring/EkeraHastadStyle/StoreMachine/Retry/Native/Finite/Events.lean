/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Resources
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
import Mathlib.Data.Finset.Card

/-!
# Scalar observations of the actual finite-retry native budget

Every positive batch count pays for each bank zero preparation and seed X, the same sampled
and recovered batch allowance per round, and the final optional selector.
These formulas observe the independent event pool. Their equalities do not
assert that every execution takes every branch listed in that allowance.
Classical operations retain their own literal coordinates and unit weight.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

open Execution ShortDLP.CompiledMAU

/-- The first bank pays for every zero preparation and every literal seed-loading X. -/
lemma eventEnvelope_succ (N count : Nat) :
    eventEnvelope N (count + 1) =
      (ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) •
        ResourcePool.singleton (model := RuntimeRound.model) (.preparation (2 : ℕ+)) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N •
        ResourcePool.singleton (model := RuntimeRound.model) (.gate .singleQubit)) +
      (count + 1) • NativeBatchReuseRecovery.eventEnvelope N +
      NativeRetrySelection.selectionEnvelope N (count + 1) := by
  simp only [eventEnvelope, NativeRetrySelection.eventEnvelope, NativeRetryChain.eventEnvelope,
    NativeRetryChain.suffixEventEnvelope, NativeBatchRecovery.eventEnvelope,
    NativeBatch.nativeEnvelope, NativeBatchReuseRecovery.eventEnvelope,
    NativeBatchReuse.nativeEnvelope, succ_nsmul]
  ac_rfl

/-- Additive observations retain the separately charged zero preparations and seed X gates. -/
lemma eventEnvelope_weighted_succ (N count : Nat)
    (weight : Resource.Event RuntimeRound.model → Nat) :
    ResourcePool.weightedCount weight (eventEnvelope N (count + 1)) =
      ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) *
          weight (.preparation (2 : ℕ+)) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N *
          weight (.gate .singleQubit) +
      (count + 1) * ResourcePool.weightedCount weight (NativeBatchReuseRecovery.eventEnvelope N) +
      ResourcePool.weightedCount weight
        (NativeRetrySelection.selectionEnvelope N (count + 1)) := by
  rw [eventEnvelope_succ]
  simp only [ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, one_mul]

/-- Closed batch-count formula for the independent total native-event allowance. -/
def eventCountBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      (44 * modulusBits N + 166 +
        16 * (RuntimeRound.eventEnvelope
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).card +
        (LatticeFixedBatchRecoveryMachine.eventEnvelope
          (model := RuntimeRound.model) N).card) +
      ShortDLP.totalQubits
        (ShortDLP.CompiledMAU.registerParameters
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
      reloadXCount (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N + 1

/-- Its scalar cardinality pays for each initial zero and X, followed by the one final pack. -/
lemma eventEnvelope_card (N totalRounds : Nat) :
    (eventEnvelope N totalRounds).card = eventCountBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [eventEnvelope_succ]
      simp only [Multiset.card_add, ResourcePool.singleton, Multiset.card_replicate,
        Multiset.card_nsmul, NativeBatchReuseRecovery.eventEnvelope,
        NativeBatchReuse.nativeEnvelope,
        ShorStyle.Canonical.Sampler.Retained.samplerRetainedEnvelope_card,
        NativeRetrySelection.selectionEnvelope,
        ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation.eventEnvelope_card,
        eventCountBound, modulusBits]
      ring

private lemma weighted_mono (weight : Resource.Event RuntimeRound.model → Nat)
    {left right : ResourcePool RuntimeRound.model} (bounded : left ≤ right) :
    ResourcePool.weightedCount weight left ≤ ResourcePool.weightedCount weight right := by
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp bounded
  rw [ResourcePool.weightedCount_add]
  exact Nat.le_add_right _ _

private lemma selector_classicalWeight (N length : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (NativeRetrySelection.selectionEnvelope N length) = 3 * length + 1 := by
  simp [NativeRetrySelection.selectionEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.Optional.Allocation.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.Optional.eventEnvelope,
    ClassicalRoutines.FirstAccepted.Direct.copyTrace, ResourcePool.scale,
    Resource.Event.classicalOperationWeight, Nat.mul_comm]
  omega

/-- Literal classical-operation count has no charge for the initial quantum preparation. -/
def classicalOperationBound (N : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => (count + 1) *
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        (NativeBatchReuseRecovery.eventEnvelope N) + 3 * (count + 1) + 1

/-- All repeated classical instructions and the selector contribute their literal unit weights. -/
lemma eventEnvelope_classicalWeight (N totalRounds : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope N totalRounds) = classicalOperationBound N totalRounds := by
  cases totalRounds with
  | zero => rfl
  | succ count =>
      rw [eventEnvelope_weighted_succ, selector_classicalWeight]
      simp only [Resource.Event.classicalOperationWeight, Nat.mul_zero, Nat.zero_add]
      exact (Nat.add_assoc _ _ _).symm

private lemma reloadLabel_zero_or_power (m ell width N : Nat) :
    (reloadLabel m ell width N).val = 0 ∨
      (reloadLabel m ell width N).val = 2 ^ width := by
  simp only [reloadLabel, ShortDLP.tripleIndex, UnitaryCircuit.prodEquiv_value,
    Fin.val_zero, Nat.mul_zero, Nat.add_zero]
  unfold cleanUnitLabel workspaceEncoding MAU.Multiplication.Accumulate.Gidney.encoding
  simp only [BinaryLabelEncoding.prod_encode, BinaryLabelEncoding.finIdentity_encode,
    UnitaryCircuit.prodEquiv_value]
  by_cases positive : 0 < N
  · by_cases fitted : N ≤ 2 ^ width
    · simp only [cleanWorkspace, dif_pos positive, dif_pos fitted, Fin.val_zero,
        Nat.zero_add, Nat.FixedWidth.unitResidueWord_one_val]
      have residue : 1 % N = 0 ∨ 1 % N = 1 := by
        have bounded := Nat.mod_le 1 N
        omega
      rcases residue with zero | one
      · simp only [zero, Nat.mul_zero, true_or]
      · simp only [one, Nat.mul_one]
        exact Or.inr rfl
    · simp [cleanWorkspace, positive, fitted, zeroWorkspace]
  · simp [cleanWorkspace, positive, zeroWorkspace]

/-- The source identity seed has at most one set bit, including the total fallback branches. -/
lemma seedReload_count_le_one (m ell width N : Nat) :
    reloadXCount m ell width N ≤ 1 := by
  rw [reloadXCount, ← List.toFinset_card_of_nodup
    (EncodedBit.Word.constantOneIndices_nodup (reloadLabel m ell width N))]
  apply Finset.card_le_one.mpr
  intro left leftMember right rightMember
  have leftBit := (EncodedBit.Word.mem_constantOneIndices _ left).mp
    (List.mem_toFinset.mp leftMember)
  have rightBit := (EncodedBit.Word.mem_constantOneIndices _ right).mp
    (List.mem_toFinset.mp rightMember)
  rcases reloadLabel_zero_or_power m ell width N with zero | power
  · simp only [zero, Nat.zero_testBit, Bool.false_eq_true] at leftBit
  · rw [power, Nat.testBit_two_pow] at leftBit rightBit
    apply Fin.ext
    exact (of_decide_eq_true leftBit).symm.trans (of_decide_eq_true rightBit)

/-- Every EH parameter choice has two nonempty exponent registers in its complete bank. -/
lemma bank_qubits_ge_three (N : Nat) :
    3 ≤ ShortDLP.totalQubits
      (ShortDLP.CompiledMAU.registerParameters
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) := by
  rw [totalQubits_eq]
  unfold tradeoffBits shortLogBits
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The scalar native-event allowance bounds each path of the same complete actual run. -/
lemma run_eventCount_le_scalar (specification : Input N) (totalRounds : Nat)
    (path : (run base noQuantum specification totalRounds).code.Path) :
    ((run base noQuantum specification totalRounds).code.eventTrace path).length ≤
      eventCountBound N totalRounds :=
  (run_eventCount_le base noQuantum specification totalRounds path).trans_eq
    (eventEnvelope_card N totalRounds)

/-- The literal classical operations on the same actual path obey the independent scalar formula. -/
lemma run_classicalOperation_le (specification : Input N) (totalRounds : Nat)
    (path : (run base noQuantum specification totalRounds).code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((run base noQuantum specification totalRounds).code.resourcePool path) ≤
      classicalOperationBound N totalRounds :=
  (weighted_mono Resource.Event.classicalOperationWeight
    (run_pool_le base noQuantum specification totalRounds path)).trans_eq
      (eventEnvelope_classicalWeight N totalRounds)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
