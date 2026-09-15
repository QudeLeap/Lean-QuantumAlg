/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.Modular.NativePower.LayoutLaws
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Real base, modulus and accumulator initialization

The base comes from the original structural read. The actual constant-loader
instructions materialize the modulus, and increment acts on the accumulator's
proved freshly allocated zero. Every original input remains unchanged before
the exponent circuit starts, including correlations carried by those cells.
-/

namespace QuantumAlg.ClassicalRoutines.Modular.NativePower

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual store after base unpacking and the complete literal modulus loader. -/
def loadedStore (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (store : Store (powerCtx ctx width)) : Store (powerCtx ctx width) :=
  (ConstantWord.foldStep (modulusCell ctx width)
    (List.ofFn (ConstantWord.constantBits (width + 1) spec.modulus))
    (store.applyOp (unpackBaseOp base))).1

/-- Actual store after the accumulator's one real initialization increment. -/
def initializedStore (spec : ModulusSpec width) (base : CInputRef ctx (.canonicalResidue width))
    (store : Store (powerCtx ctx width)) : Store (powerCtx ctx width) :=
  (loadedStore spec base store).applyOp (initializeOp ctx width)

private theorem keyFree {written observed : CShape} (write : CWriteRef ctx written)
    (read : CWriteRef ctx observed) (different : write.key ≠ read.key) :
    write.key ∉ (wordRead read).storageKeys :=
  fun present => different (List.mem_singleton.mp present)

/-- Every original input is still the same structural value when the power loop begins. -/
theorem nativePower_initialized_read_original (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) :
    (initializedStore spec base (enterPower store width)).read (underPower other width) =
      store.read other := by
  have separated := nativePower_input_separation other width
  unfold initializedStore loadedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeOp ctx width)
    (underPower other width) separated.2.2]
  rw [ConstantWord.constantWord_fold_read_other (modulusCell ctx width) _
    (underPower other width) separated.1]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (unpackBaseOp base)
    (underPower other width) separated.2.1]
  exact nativePower_enterPower_read store other width

/-- The actual raw base word is exactly the unpacking of the original nominal base read. -/
theorem nativePower_initialized_base (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx) :
    (initializedStore spec base (enterPower store width)).read (wordRead (baseCell ctx width)) =
      CShape.unpackCanonicalResidue width (store.read base) := by
  have separated := nativePower_scope_separation ctx width
  unfold initializedStore loadedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeOp ctx width)
    (wordRead (baseCell ctx width))
    (keyFree (accumulatorCell ctx width) (baseCell ctx width) separated.2.2)]
  rw [ConstantWord.constantWord_fold_read_other (modulusCell ctx width) _
    (wordRead (baseCell ctx width))
    (keyFree (modulusCell ctx width) (baseCell ctx width) separated.1)]
  change ((enterPower store width).applyOp (unpackBaseOp base)).read
    (.storage (unpackBaseOp base).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.unpackCanonicalResidue width
    ((enterPower store width).read (underPower base width)) = _
  rw [nativePower_enterPower_read]

/-- The actual modulus word contains the complete source modulus, including at capacity. -/
theorem nativePower_initialized_modulus_toNat (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx) :
    ((initializedStore spec base (enterPower store width)).read
      (wordRead (modulusCell ctx width))).toNat = spec.modulus := by
  have separated := nativePower_scope_separation ctx width
  unfold initializedStore
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (initializeOp ctx width)
    (wordRead (modulusCell ctx width))
    (keyFree (accumulatorCell ctx width) (modulusCell ctx width) separated.2.1)]
  exact (ConstantWord.constantWord_read (modulusCell ctx width) spec.modulus
    ((enterPower store width).applyOp (unpackBaseOp base))).trans
    (Nat.mod_eq_of_lt (modulusSpec_modulus_lt_extended spec))

/-- The finite modulus encoding is precisely the intrinsic specification's extended word. -/
theorem nativePower_initialized_modulus (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx) :
    (initializedStore spec base (enterPower store width)).read (wordRead (modulusCell ctx width)) =
      .unsignedWord spec.extendedWord := by
  have actual := nativePower_initialized_modulus_toNat spec base store
  cases sampled : (initializedStore spec base (enterPower store width)).read
      (wordRead (modulusCell ctx width)) with
  | unsignedWord value =>
      rw [sampled] at actual
      exact congrArg CShape.Value.unsignedWord (Fin.ext actual)

/-- Earlier base and modulus writes preserve the actual fresh-zero accumulator. -/
theorem nativePower_loaded_accumulator (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx) :
    (loadedStore spec base (enterPower store width)).read (wordRead (accumulatorCell ctx width)) =
      CShape.wordOfNat width 0 := by
  have separated := nativePower_scope_separation ctx width
  unfold loadedStore
  rw [ConstantWord.constantWord_fold_read_other (modulusCell ctx width) _
    (wordRead (accumulatorCell ctx width))
    (keyFree (modulusCell ctx width) (accumulatorCell ctx width) (Ne.symm separated.2.1))]
  rw [Store.read_applyOp_of_not_mem_storageKeys _ (unpackBaseOp base)
    (wordRead (accumulatorCell ctx width))
    (keyFree (baseCell ctx width) (accumulatorCell ctx width) (Ne.symm separated.2.2))]
  exact nativePower_enterPower_accumulator store width

/-- The initialization increment therefore writes one modulo the actual accumulator capacity. -/
theorem nativePower_initialized_accumulator (spec : ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width)) (store : Store ctx) :
    (initializedStore spec base (enterPower store width)).read
      (wordRead (accumulatorCell ctx width)) = CShape.wordOfNat width 1 := by
  change ((loadedStore spec base (enterPower store width)).applyOp (initializeOp ctx width)).read
    (.storage (initializeOp ctx width).outputRef.toCStorageRef) = _
  rw [Store.read_applyOp_output]
  change CShape.wordOfNat width
    (((loadedStore spec base (enterPower store width)).read
      (wordRead (accumulatorCell ctx width))).toNat + 1) = _
  rw [nativePower_loaded_accumulator]
  simp only [CShape.wordOfNat_val, Nat.zero_mod, Nat.zero_add]

end

end QuantumAlg.ClassicalRoutines.Modular.NativePower
