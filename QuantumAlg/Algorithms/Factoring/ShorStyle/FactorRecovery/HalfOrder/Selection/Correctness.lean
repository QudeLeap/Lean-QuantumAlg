/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Values
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Correctness
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Preservation

/-!
# Source-prescribed left-priority factor recovery from the actual stored half-power

Both candidate GCDs come from their actual scoped Euclidean execution. The
real stored comparisons and nominal packaging agree with the original
natural-number selector, including rejection and strict left priority. The
physical separation conditions are discharged by the six-cell scope; they
are properties of its real references, not new source-input conditions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor

open ClassicalRoutines.NumberTheory

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The actual structural inputs that must survive either candidate computation and its checks. -/
def stableOperands (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) : CInputRef ctx
      (.product (.unsignedWord (modulusBits N))
        (.product (.unsignedWord (modulusBits N + 1)) (.unsignedWord (modulusBits N + 1)))) :=
  .product halfPower (.product cells.one cells.modulus)

/-- Physical cell separation established by the real enclosing lexical allocations. -/
structure Separation (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) : Prop where
  candidateStable : cells.candidate.key ∉ (stableOperands halfPower cells).storageKeys
  lowerStable : cells.lower.key ∉ (stableOperands halfPower cells).storageKeys
  upperStable : cells.upper.key ∉ (stableOperands halfPower cells).storageKeys
  lowerCandidate : cells.lower.key ≠ cells.candidate.key
  upperCandidate : cells.upper.key ≠ cells.candidate.key
  upperLower : cells.upper.key ≠ cells.lower.key
  payloadLower : cells.payload.key ≠ cells.lower.key

private lemma lower_check_free
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (separate : Separation halfPower cells) :
    cells.lower.key ∉
      (CInputRef.product (.storage cells.candidate.toCStorageRef) cells.modulus).storageKeys := by
  intro member
  rcases List.mem_append.mp member with candidate | modulus
  · exact separate.lowerCandidate (List.mem_singleton.mp candidate)
  · exact separate.lowerStable (List.mem_append_right halfPower.storageKeys
      (List.mem_append_right cells.one.storageKeys modulus))

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private lemma choose_read (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (cells : Cells ctx N) (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (store : Store ctx) :
    (chooseStep (model := model) halfPower cells output store).1.read (.storage
        output.toCStorageRef) =
      if (store.read (.storage cells.lower.toCStorageRef)).toBool then
        (packStep (model := model) cells output store).1.read (.storage output.toCStorageRef)
      else (rightStep (model := model) halfPower cells output store).1.read (.storage
          output.toCStorageRef) := by
  simp only [chooseStep]
  cases store.read (.storage cells.lower.toCStorageRef) with
  | bit value => cases value <;> rfl

private lemma right_result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : Separation halfPower cells)
    (oneValue : (store.read cells.one).toNat = 1)
    (modulusValue : (store.read cells.modulus).toNat = N) :
    (rightStep (model := model) halfPower cells output store).1.read (.storage
        output.toCStorageRef) =
      encodeOutput (N := N)
        (let candidate := Nat.gcd ((store.read halfPower).toNat + 1) N
         if 1 < candidate ∧ candidate < N then some candidate else none) := by
  let reduced := NativeHalfGCD.step (model := model) true halfPower cells.candidate store
  have preserved := NativeHalfGCD.read_other (model := model) true halfPower cells.candidate
    (stableOperands halfPower cells) separate.candidateStable store
  have oneSame : (reduced.1.read cells.one).toNat = 1 :=
    (congrArg (fun value => value.second.first.toNat) preserved).trans oneValue
  have modulusSame : (reduced.1.read cells.modulus).toNat = N :=
    (congrArg (fun value => value.second.second.toNat) preserved).trans modulusValue
  have candidate : (reduced.1.read (.storage cells.candidate.toCStorageRef)).toNat =
      Nat.gcd ((store.read halfPower).toNat + 1) N :=
    NativeHalfGCD.result_toNat (model := model) source true halfPower cells.candidate store
  have packed := checkedPack_result (model := model) cells output reduced.1
    (lower_check_free halfPower cells separate) separate.upperLower separate.upperCandidate
    separate.payloadLower
  refine packed.trans ?_
  rw [oneSame, modulusSame, candidate]
  by_cases lower : 1 < Nat.gcd ((store.read halfPower).toNat + 1) N
  · by_cases upper : Nat.gcd ((store.read halfPower).toNat + 1) N < N
    · simp [lower, upper, encodeOutput]
    · simp [lower, upper, encodeOutput]
  · simp [lower, encodeOutput]

/-- The physical left-priority circuit returns exactly the original pure half-power selector. -/
lemma result (source : Input N)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) (store : Store ctx)
    (separate : Separation halfPower cells)
    (oneValue : (store.read cells.one).toNat = 1)
    (modulusValue : (store.read cells.modulus).toNat = N) :
    (step (model := model) halfPower cells output store).1.read (.storage output.toCStorageRef) =
      encodeOutput (N := N) (factorFromHalfPowerValue N (store.read halfPower).toNat) := by
  let reduced := NativeHalfGCD.step (model := model) false halfPower cells.candidate store
  let compared := FactorRange.storeStep (checkRefs cells) reduced.1
  have reducedStable := NativeHalfGCD.read_other (model := model) false halfPower cells.candidate
    (stableOperands halfPower cells) separate.candidateStable store
  have comparedStable := FactorRange.read_other (checkRefs cells)
    (stableOperands halfPower cells) separate.lowerStable separate.upperStable reduced.1
  have stable := comparedStable.trans reducedStable
  have halfSame : compared.read halfPower = store.read halfPower :=
    congrArg CShape.Value.first stable
  have oneSame : (reduced.1.read cells.one).toNat = 1 :=
    (congrArg (fun value => value.second.first.toNat) reducedStable).trans oneValue
  have modulusSame : (reduced.1.read cells.modulus).toNat = N :=
    (congrArg (fun value => value.second.second.toNat) reducedStable).trans modulusValue
  have candidate : (reduced.1.read (.storage cells.candidate.toCStorageRef)).toNat =
      Nat.gcd ((store.read halfPower).toNat - 1) N :=
    NativeHalfGCD.result_toNat (model := model) source false halfPower cells.candidate store
  have tag : (compared.read (.storage cells.lower.toCStorageRef)).toBool =
      (decide ((reduced.1.read cells.one).toNat <
          (reduced.1.read (.storage cells.candidate.toCStorageRef)).toNat) &&
        decide ((reduced.1.read (.storage cells.candidate.toCStorageRef)).toNat <
          (reduced.1.read cells.modulus).toNat)) :=
    FactorRange.result (checkRefs cells) reduced.1
      (lower_check_free halfPower cells separate) separate.upperLower
  have tagValue : (compared.read (.storage cells.lower.toCStorageRef)).toBool =
      (decide (1 < Nat.gcd ((store.read halfPower).toNat - 1) N) &&
        decide (Nat.gcd ((store.read halfPower).toNat - 1) N < N)) := by
    exact tag.trans (by rw [oneSame, modulusSame, candidate])
  have candidateSame := FactorRange.read_other (checkRefs cells)
    (.storage cells.candidate.toCStorageRef)
    (fun member => separate.lowerCandidate (List.mem_singleton.mp member))
    (fun member => separate.upperCandidate (List.mem_singleton.mp member)) reduced.1
  change (chooseStep (model := model) halfPower cells output compared).1.read (.storage
      output.toCStorageRef) = _
  rw [choose_read, tagValue]
  by_cases accepted : 1 < Nat.gcd ((store.read halfPower).toNat - 1) N ∧
      Nat.gcd ((store.read halfPower).toNat - 1) N < N
  · have active : (decide (1 < Nat.gcd ((store.read halfPower).toNat - 1) N) &&
        decide (Nat.gcd ((store.read halfPower).toNat - 1) N < N)) = true := by
      simp only [accepted.1, accepted.2, decide_true, Bool.true_and]
    rw [active, if_pos rfl, pack_result_numeric (model := model) cells output compared
        separate.payloadLower,
      tagValue, active, if_pos rfl, candidateSame, candidate]
    simp [factorFromHalfPowerValue, accepted, encodeOutput]
  · have inactive : (decide (1 < Nat.gcd ((store.read halfPower).toNat - 1) N) &&
        decide (Nat.gcd ((store.read halfPower).toNat - 1) N < N)) = false := by
      rw [← Bool.decide_and]
      exact decide_eq_false accepted
    rw [inactive, if_neg (by decide : ¬ (false = true))]
    have next := right_result (model := model) source halfPower cells output compared separate
      ((congrArg (fun value => value.second.first.toNat) stable).trans oneValue)
      ((congrArg (fun value => value.second.second.toNat) stable).trans modulusValue)
    refine next.trans ?_
    rw [halfSame]
    simp only [factorFromHalfPowerValue, accepted, if_false]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactor
