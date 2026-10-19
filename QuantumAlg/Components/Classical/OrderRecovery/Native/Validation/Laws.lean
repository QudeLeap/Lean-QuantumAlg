/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Validation

/-!
# Exact Boolean semantics of actual candidate validation

The actual modular-power result and the three stored comparison operations
produce positivity conjoined with modular return. Fresh placement later
discharges the internal read/write separation conditions. No correctness or
resource witness is passed to the executable validation program.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

private lemma positive_read (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (positive : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (candidatePositiveOp zero candidate positive)).read (cellRead positive) =
      .bit (decide ((store.read zero).toNat < (store.read candidate).toNat)) :=
  Store.read_applyOp_output store (candidatePositiveOp zero candidate positive)

private lemma return_read (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (valid : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (candidateReturnOp power one valid)).read (cellRead valid) =
      .bit (decide ((store.read power).toNat = (store.read one).toNat)) :=
  Store.read_applyOp_output store (candidateReturnOp power one valid)

private lemma conjunction_read (positive valid : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (candidateValidOp positive valid)).read (cellRead valid) =
      .bit ((store.read (cellRead positive)).toBool && (store.read (cellRead valid)).toBool) := by
  refine (Store.read_applyOp_output store (candidateValidOp positive valid)).trans ?_
  change Resource.BitOpcode.eval .and
    (.product (store.read (cellRead positive)) (store.read (cellRead valid))) = _
  cases store.read (cellRead positive)
  cases store.read (cellRead valid)
  rfl

/-- The three real checks conjoin comparisons of the original stored operands. -/
lemma nativeValidation_checks_result
    (zero candidate : CInputRef ctx (.unsignedWord candidateWidth))
    (power one : CInputRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit)
    (different : valid.key ≠ positive.key)
    (powerFree : positive.key ∉ power.storageKeys)
    (oneFree : positive.key ∉ one.storageKeys) (store : Store ctx) :
    (validationChecksStore zero candidate power one positive valid store).read (cellRead valid) =
      .bit (decide ((store.read zero).toNat < (store.read candidate).toNat) &&
        decide ((store.read power).toNat = (store.read one).toNat)) := by
  unfold validationChecksStore
  rw [conjunction_read,
    Store.read_applyOp_of_not_mem_storageKeys _ (candidateReturnOp power one valid)
      (cellRead positive) (fun present => different (List.mem_singleton.mp present)),
    return_read, positive_read,
    Store.read_applyOp_of_not_mem_storageKeys store (candidatePositiveOp zero candidate positive)
      power powerFree,
    Store.read_applyOp_of_not_mem_storageKeys store (candidatePositiveOp zero candidate positive)
      one oneFree]
  rfl

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual candidate validation computes positivity and modular return of the represented input. -/
lemma nativeValidation_result (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit)
    (different : valid.key ≠ positive.key)
    (positivePower : positive.key ≠ power.key)
    (positiveOne : positive.key ∉ one.storageKeys)
    (powerCandidate : power.key ∉ candidate.storageKeys)
    (powerZero : power.key ∉ zero.storageKeys)
    (powerOne : power.key ∉ one.storageKeys) (store : Store ctx)
    (input : Pow.Input spec candidateWidth)
    (represented : Modular.NativePower.InputRepresents spec base candidate store input)
    (zeroValue : (store.read zero).toNat = 0)
    (oneValue : (store.read one).toNat = 1) :
    ((validateStep (model := model) spec base candidate zero one power positive valid store).1).read
      (cellRead valid) =
        .bit (decide (0 < input.exponent.val) &&
          decide (input.base.val ^ input.exponent.val % spec.modulus = 1)) := by
  change (validationChecksStore zero candidate (cellRead power) one positive valid
    (Modular.NativePower.intoStep (model := model) spec base candidate power store).1).read
      (cellRead valid) = _
  have powerValue :
      (((Modular.NativePower.intoStep (model := model) spec base candidate power store).1).read
        (cellRead power)).toNat = input.base.val ^ input.exponent.val % spec.modulus :=
    Modular.NativePower.nativePower_into_toNat (model := model) spec base candidate power
      store input represented
  rw [nativeValidation_checks_result zero candidate (cellRead power) one positive valid different
    (fun present => positivePower (List.mem_singleton.mp present)) positiveOne,
    Modular.NativePower.nativePower_into_read_other (model := model) spec base candidate power
      store zero powerZero,
    Modular.NativePower.nativePower_into_read_other (model := model) spec base candidate power
      store candidate
      powerCandidate,
    Modular.NativePower.nativePower_into_read_other (model := model) spec base candidate power
      store one powerOne,
    powerValue,
    zeroValue, oneValue, represented.2]
  rfl

/-- Validation changes no original structural input beyond its power and two comparison cells. -/
lemma nativeValidation_read_other (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord candidateWidth))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth))
    (positive valid : CWriteRef ctx .bit) {shape : CShape} (other : CInputRef ctx shape)
    (powerFree : power.key ∉ other.storageKeys)
    (positiveFree : positive.key ∉ other.storageKeys)
    (validFree : valid.key ∉ other.storageKeys) (store : Store ctx) :
    ((validateStep (model := model) spec base candidate zero one power positive valid store).1).read
      other =
      store.read other := by
  unfold validateStep validationChecksStep
  simp only [BitWord.instructionStep]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (candidateValidOp positive valid) other validFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (candidateReturnOp (cellRead power) one valid)
      other validFree,
    Store.read_applyOp_of_not_mem_storageKeys _ (candidatePositiveOp zero candidate positive)
      other positiveFree,
    Modular.NativePower.nativePower_into_read_other (model := model) spec base candidate power
      store other powerFree]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
