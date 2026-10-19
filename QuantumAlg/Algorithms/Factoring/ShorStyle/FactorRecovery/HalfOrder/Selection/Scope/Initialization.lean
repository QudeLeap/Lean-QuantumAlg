/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Keys
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Components.Classical.ConstantWord.Semantics

/-!
# Actual constant initialization of the half-factor scope

The same native shift-and-increment constant programs load the physical one
and widened modulus words. Their actual fresh keys preserve every original
structural input, and the second load preserves the first constant. These
facts hold for every store of the real extended context.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope

open Execution ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

/-- The exact real record of the first compiled constant-word program. -/
def oneStep (store : Store (context ctx N)) : Store (context ctx N) ×
    (ConstantWord.circuit (model := model) (oneRef ctx N) 1).Path :=
  ConstantWord.foldStep (model := model) (oneRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) 1)) store

/-- The exact real record of the second compiled constant-word program. -/
def modulusStep (store : Store (context ctx N)) : Store (context ctx N) ×
    (ConstantWord.circuit (model := model) (modulusRef ctx N) N).Path :=
  ConstantWord.foldStep (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) store

/-- The actual store after both constant programs, retaining all the other real cells. -/
def initialized (store : Store (context ctx N)) : Store (context ctx N) :=
  (modulusStep (model := model) (oneStep (model := model) store).1).1

/-- The second native constant load preserves the exact physical one written by the first. -/
lemma initialized_one (store : Store (context ctx N)) :
    ((initialized (model := model) store).read (.storage (oneRef ctx N).toCStorageRef)).toNat = 1
        := by
  have separate : (modulusRef ctx N).key ∉
      (CInputRef.storage (oneRef ctx N).toCStorageRef).storageKeys :=
    fun member => scratchKeys_ne ctx N 3 4 (by decide) (List.mem_singleton.mp member)
  have preserved := ConstantWord.constantWord_fold_read_other (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N))
    (.storage (oneRef ctx N).toCStorageRef) separate (oneStep (model := model) store).1
  refine (congrArg CShape.Value.toNat preserved).trans
    ((ConstantWord.constantWord_read (model := model) (oneRef ctx N) 1 store).trans ?_)
  apply Nat.mod_eq_of_lt
  have positive := Nat.two_pow_pos (modulusBits N)
  have doubled := Nat.pow_succ 2 (modulusBits N)
  omega

/-- The real widened modulus load retains the original modulus without truncation. -/
lemma initialized_modulus (source : Input N) (store : Store (context ctx N)) :
    ((initialized (model := model) store).read (.storage (modulusRef ctx N).toCStorageRef)).toNat
        = N := by
  refine (ConstantWord.constantWord_read (model := model) (modulusRef ctx N) N (oneStep (model :=
      model) store).1).trans ?_
  apply Nat.mod_eq_of_lt
  have fits := source.register_fits
  have positive := Nat.two_pow_pos (modulusBits N)
  have doubled := Nat.pow_succ 2 (modulusBits N)
  omega

/-- Both actual constant loads preserve the same original structural operand beneath the scope. -/
lemma initialized_read_original {shape : CShape} (input : CInputRef ctx shape)
    (store : Store (context ctx N)) :
    (initialized (model := model) store).read (liftInput input) = store.read (liftInput input) :=
  (ConstantWord.constantWord_fold_read_other (model := model) (modulusRef ctx N)
    (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) N)) (liftInput input)
    (scratchKeys_input_separate input _ (List.get_mem (scratchKeys ctx N) (3 : Fin 6)))
    (oneStep (model := model) store).1).trans
    (ConstantWord.constantWord_fold_read_other (model := model) (oneRef ctx N)
      (List.ofFn (ConstantWord.constantBits (modulusBits N + 1) 1)) (liftInput input)
      (scratchKeys_input_separate input _ (List.get_mem (scratchKeys ctx N) (4 : Fin 6))) store)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfFactorScope
