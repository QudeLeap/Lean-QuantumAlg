/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Layout.Laws
import all
  QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Correctness

/-!
# Actual adjacent half-power GCD values

The native program reads the stored half-power, forms its exact natural
adjacent value, loads the true modulus and runs the same expanded Euclidean
circuit. Every initialization and storage-separation fact follows from the
actual code and its two real lexical allocations. The only source input
condition is the original nontrivial-modulus contract.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD

open Execution ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

private lemma gcdTail_result (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) :
    ((gcdTailStep (model := model) output store).1.read (.storage (liftWrite
      output).toCStorageRef)).toNat =
      Nat.gcd (store.read (.storage (adjacentRef ctx N).toCStorageRef)).toNat
        (store.read (.storage (modulusRef ctx N).toCStorageRef)).toNat := by
  let cleared := store.applyOp (clearOp output)
  have zeroValue : (cleared.read (.storage (liftWrite output).toCStorageRef)).toNat = 0 :=
    (congrArg CShape.Value.toNat (Store.read_applyOp_output store (clearOp output))).trans
      (NativeAdjacentWord.selfXor_toNat (store.read (.storage (liftWrite output).toCStorageRef)))
  have free : (clearOp output).outputRef.key ∉ (operands ctx N).storageKeys := by
    change (liftWrite (N := N) output).key ∉
      [(adjacentRef ctx N).key, (modulusRef ctx N).key]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨output_ne_adjacent output, output_ne_modulus output⟩
  have unchanged := Store.read_applyOp_of_not_mem_storageKeys store
    (clearOp output) (operands ctx N) free
  have actual := NumberTheory.GCD.gcdLexical_read_result (model := model) (operands ctx N)
    (liftWrite output) cleared zeroValue
  refine (congrArg CShape.Value.toNat actual).trans ?_
  rw [unchanged]
  change (encodeWord (ClassicalAlgorithms.NumberTheory.GCD.eval
    (NumberTheory.GCD.decodeOperands
      (.product (store.read (.storage (adjacentRef ctx N).toCStorageRef))
        (store.read (.storage (modulusRef ctx N).toCStorageRef)))))).toNat = _
  cases store.read (.storage (adjacentRef ctx N).toCStorageRef) with
  | unsignedWord left =>
      cases store.read (.storage (modulusRef ctx N).toCStorageRef) with
      | unsignedWord right => rfl

private lemma loadTail_result (source : Input N)
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) :
    ((loadTailStep (model := model) output store).1.read (.storage (liftWrite
      output).toCStorageRef)).toNat =
      Nat.gcd (store.read (.storage (adjacentRef ctx N).toCStorageRef)).toNat N := by
  let loaded := ConstantWord.foldStep (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store
  have separated : (modulusRef ctx N).key ∉
      (CInputRef.storage (adjacentRef ctx N).toCStorageRef).storageKeys := by
    change (modulusRef ctx N).key ∉ [(adjacentRef ctx N).key]
    exact fun member => adjacent_ne_modulus ctx N (List.mem_singleton.mp member).symm
  have adjacentSame := ConstantWord.constantWord_fold_read_other (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N))
    (.storage (adjacentRef ctx N).toCStorageRef) separated store
  have modulusSame : (loaded.1.read (.storage (modulusRef ctx N).toCStorageRef)).toNat = N := by
    refine (ConstantWord.constantWord_read (model := model) (modulusRef ctx N) N store).trans ?_
    apply Nat.mod_eq_of_lt
    have fits := source.register_fits
    have positive := Nat.two_pow_pos (modulusBits N)
    have doubled := Nat.pow_succ 2 (modulusBits N)
    omega
  exact (gcdTail_result (model := model) output loaded.1).trans
    (congrArg₂ Nat.gcd (congrArg CShape.Value.toNat adjacentSame) modulusSame)

/-- The genuine body returns the original GCD of the stored half-power's natural adjacent value. -/
lemma body_result (source : Input N) (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1)))
    (store : Store (context ctx N)) :
    ((bodyStep (model := model) successor halfPower output store).1.read
      (.storage (liftWrite output).toCStorageRef)).toNat =
      Nat.gcd
        (if successor then (store.read (liftInput halfPower)).toNat + 1
          else (store.read (liftInput halfPower)).toNat - 1) N :=
  (loadTail_result (model := model) source output
    (NativeAdjacentWord.step (model := model) successor (liftInput halfPower) (adjacentRef ctx N)
      store).1).trans
    (congrArg (fun adjacent => Nat.gcd adjacent N)
      (NativeAdjacentWord.result_toNat (model := model) successor (liftInput halfPower)
        (adjacentRef ctx N) store))

/-- Actual scope exit exposes exactly the original left or right half-power GCD. -/
lemma result_toNat (source : Input N) (successor : Bool)
    (halfPower : CInputRef ctx (.unsignedWord (modulusBits N)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N + 1))) (store : Store ctx) :
    ((step (model := model) successor halfPower output store).1.read (.storage
      output.toCStorageRef)).toNat =
      Nat.gcd
        (if successor then (store.read halfPower).toNat + 1 else (store.read halfPower).toNat - 1)
        N := by
  have popped := popStore_read (.storage output.toCStorageRef)
    (bodyStep (model := model) successor halfPower output (pushStore N store)).1
  refine (congrArg CShape.Value.toNat popped).trans
    ((body_result (model := model) source successor halfPower output (pushStore N store)).trans ?_)
  exact congrArg (fun half : CShape.Word (modulusBits N) =>
    Nat.gcd (if successor then half.toNat + 1 else half.toNat - 1) N)
    (pushStore_read halfPower store)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfGCD
