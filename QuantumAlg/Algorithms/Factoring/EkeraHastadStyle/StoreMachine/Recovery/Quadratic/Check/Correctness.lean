/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Check.Program
import all QuantumAlg.Components.Classical.NumberTheory.Nat.ModCheck.Correctness

/-!
# Exact actual quadratic candidate predicates and unconditional caller frames
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck

open Execution
open ClassicalRoutines.NumberTheory

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {shortWidth : Nat}

omit [BitWord.Selected model] in
private lemma positiveSeed_frame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (wide : refs.candidateWide.key ∉ other.storageKeys)
    (below : refs.belowModulus.key ∉ other.storageKeys) :
    (positiveSeed refs store).read other = store.read other :=
  (Store.read_applyOp_of_not_mem_storageKeys _ (belowOp refs) other below).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (widenOp refs) other wide)

omit [BitWord.Selected model] in
private lemma widened_value (refs : Refs ctx shortWidth) (store : Store ctx) :
    ((store.applyOp (widenOp refs)).read (writeInput refs.candidateWide)).toNat =
      (store.read refs.candidate).toNat := by
  change ((store.applyOp (widenOp refs)).read
    (.storage (widenOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  apply ClassicalOp.eval_wordResize_exact
  have widthLe : CandidateWidth shortWidth ≤ ModulusWidth shortWidth := by
    simp only [CandidateWidth, ModulusWidth, QuadraticPrefix.centerWidth,
      QuadraticPrefix.discriminantWidth]
    omega
  exact (store.read refs.candidate).toNat_lt.trans_le
    (Nat.pow_le_pow_right (by omega) widthLe)

omit [BitWord.Selected model] in
private lemma below_value (refs : Refs ctx shortWidth) (separation : PositiveSeparation refs)
    (store : Store ctx) :
    ((positiveSeed refs store).read (writeInput refs.belowModulus)).toBool =
      decide ((store.read refs.candidate).toNat < (store.read refs.modulus).toNat) := by
  change (((store.applyOp (widenOp refs)).applyOp (belowOp refs)).read
    (.storage (belowOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  change decide (((store.applyOp (widenOp refs)).read (writeInput refs.candidateWide)).toNat <
    ((store.applyOp (widenOp refs)).read refs.modulus).toNat) = _
  rw [widened_value, Store.read_applyOp_of_not_mem_storageKeys store (widenOp refs)
    refs.modulus separation.modulusAvoidsWide]

omit [BitWord.Selected model] in
private lemma combine_value (refs : Refs ctx shortWidth) (store : Store ctx) :
    ((store.applyOp (combineOp refs)).read (writeInput refs.eligible)).toBool =
      ((store.read (writeInput refs.belowModulus)).toBool &&
        (store.read (writeInput refs.modulusCheck.accepted)).toBool) := by
  change ((store.applyOp (combineOp refs)).read
    (.storage (combineOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  cases below : store.read (writeInput refs.belowModulus) with
  | bit belowBit =>
      cases accepted : store.read (writeInput refs.modulusCheck.accepted) with
      | bit acceptedBit =>
          change (Resource.BitOpcode.eval .and
            (.product (store.read (writeInput refs.belowModulus))
              (store.read (writeInput refs.modulusCheck.accepted)))).toBool = _
          rw [below, accepted]
          rfl

/-- All caller reads outside the five actual positive-suffix writes are preserved. -/
lemma positiveInto_callerFrame (refs : Refs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : PositiveCallerFrameAvoids refs other) :
    (positiveStep refs store).1.read other = store.read other := by
  change (((NatModCheck.step refs.modulusCheck (positiveSeed refs store)).1.applyOp
    (combineOp refs)).read other) = _
  exact (Store.read_applyOp_of_not_mem_storageKeys _ (combineOp refs) other avoids.eligible).trans
    ((NatModCheck.into_callerFrame refs.modulusCheck _ other avoids.division
      avoids.modulusAccepted).trans
        (positiveSeed_frame refs store other avoids.candidateWide avoids.belowModulus))

/-- Positive candidates obey exactly the original range-and-divisibility specification. -/
lemma positiveInto_correct (refs : Refs ctx shortWidth) (separation : PositiveSeparation refs)
    (store : Store ctx) (initial : PositiveInitialConditions store refs) :
    PositiveRelation refs store (positiveStep refs store).1 := by
  have candidate := positiveSeed_frame refs store refs.candidate
    separation.candidateAvoidsWide separation.candidateAvoidsBelow
  have modulus := positiveSeed_frame refs store refs.modulus
    separation.modulusAvoidsWide separation.modulusAvoidsBelow
  have zero := positiveSeed_frame refs store refs.zero
    separation.zeroAvoidsWide separation.zeroAvoidsBelow
  have checkInitial :
      NatModCheck.InitialConditions (positiveSeed refs store) refs.modulusCheck := by
    constructor
    · rw [refs.modulusCheckDivisor, candidate]
      exact initial.1
    · rw [refs.modulusCheckZero, zero]
      exact initial.2.2
  have checked := NatModCheck.into_correct refs.modulusCheck separation.modulusCheck
    (positiveSeed refs store) checkInitial
  have accepted := checked.accepted
  rw [refs.modulusCheckNumerator, refs.modulusCheckDivisor, modulus, candidate] at accepted
  have belowFrame := NatModCheck.into_callerFrame refs.modulusCheck (positiveSeed refs store)
    (writeInput refs.belowModulus) separation.belowAvoidsDivision separation.belowAvoidsModAccepted
  refine ⟨?_, positiveInto_callerFrame refs store⟩
  change (((NatModCheck.step refs.modulusCheck (positiveSeed refs store)).1.applyOp
    (combineOp refs)).read (writeInput refs.eligible)).toBool = _
  rw [combine_value, belowFrame, below_value refs separation store, accepted]
  simp only [Bool.decide_and]

omit [BitWord.Selected model] in
private lemma decision_value (refs : TotalRefs ctx shortWidth) (store : Store ctx) :
    ((store.applyOp (decisionOp refs)).read (writeInput refs.greaterThanOne)).toBool =
      decide ((store.read refs.one).toNat < (store.read refs.positiveCheck.candidate).toNat) := by
  change ((store.applyOp (decisionOp refs)).read
    (.storage (decisionOp refs).outputRef.toCStorageRef)).toBool = _
  rw [Store.read_applyOp_output]
  rfl

omit [BitWord.Selected model] in
private lemma reject_value (refs : TotalRefs ctx shortWidth) (store : Store ctx) :
    ((store.applyOp (rejectOp refs)).read (writeInput refs.positiveCheck.eligible)).toBool =
      false := by
  change ((store.applyOp (rejectOp refs)).read
    (.storage (rejectOp refs).outputRef.toCStorageRef)).toBool = false
  rw [Store.read_applyOp_output]
  change (Resource.BitOpcode.eval .xor
    (.product (store.read (writeInput refs.positiveCheck.eligible))
      (store.read (writeInput refs.positiveCheck.eligible)))).toBool = false
  cases eligible : store.read (writeInput refs.positiveCheck.eligible) with
  | bit flag => exact Bool.xor_self flag

/-- Total checking frames every caller read outside its decision and possible suffix writes. -/
lemma into_callerFrame (refs : TotalRefs ctx shortWidth) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : TotalCallerFrameAvoids refs other) :
    (step refs store).1.read other = store.read other := by
  change (chooseStep refs (store.applyOp (decisionOp refs))).1.read other = _
  rw [chooseStep_store]
  split
  · exact (positiveInto_callerFrame refs.positiveCheck _ other avoids.positive).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (decisionOp refs) other avoids.decision)
  · exact (Store.read_applyOp_of_not_mem_storageKeys _ (rejectOp refs) other
      avoids.positive.eligible).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (decisionOp refs) other avoids.decision)

/-- The actual total checker accepts exactly the original strict proper-divisor predicate. -/
lemma into_correct (refs : TotalRefs ctx shortWidth) (separation : TotalSeparation refs)
    (store : Store ctx) (initial : TotalInitialConditions store refs) :
    TotalRelation refs store (step refs store).1 := by
  have candidate := Store.read_applyOp_of_not_mem_storageKeys store (decisionOp refs)
    refs.positiveCheck.candidate separation.candidateAvoidsDecision
  have modulus := Store.read_applyOp_of_not_mem_storageKeys store (decisionOp refs)
    refs.positiveCheck.modulus separation.modulusAvoidsDecision
  have zero := Store.read_applyOp_of_not_mem_storageKeys store (decisionOp refs)
    refs.positiveCheck.zero separation.zeroAvoidsDecision
  have decision := decision_value refs store
  rw [initial.1] at decision
  refine ⟨?_, into_callerFrame refs store⟩
  change ((chooseStep refs (store.applyOp (decisionOp refs))).1.read
    (writeInput refs.positiveCheck.eligible)).toBool = _
  rw [chooseStep_store]
  split
  · rename_i selected
    have greater : 1 < (store.read refs.positiveCheck.candidate).toNat :=
      of_decide_eq_true (decision.symm.trans selected)
    have positiveInitial : PositiveInitialConditions (store.applyOp (decisionOp refs))
        refs.positiveCheck := by
      change 0 < (_ : CShape.Value _).toNat ∧ 0 < (_ : CShape.Value _).toNat ∧
        (_ : CShape.Value _).toNat = 0
      rw [candidate, modulus, zero]
      exact ⟨by omega, initial.2.1, initial.2.2⟩
    have positive := (positiveInto_correct refs.positiveCheck separation.positive
      (store.applyOp (decisionOp refs)) positiveInitial).eligible
    rw [candidate, modulus] at positive
    simpa only [greater, true_and] using positive
  · rename_i selected
    have notGreater : ¬ 1 < (store.read refs.positiveCheck.candidate).toNat := by
      intro greater
      exact selected (decision.trans (decide_eq_true greater))
    rw [reject_value]
    simp only [notGreater, false_and, decide_false]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.QuadraticCandidateCheck
