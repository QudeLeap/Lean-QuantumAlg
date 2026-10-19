/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution
import all QuantumAlg.Components.Classical.Modular.NativePower.Correctness
import all QuantumAlg.Core.Execution.Store.Read

/-!
# The actual stored half-order power equals the original factor-recovery value

The fresh half-order cell cannot alias either original operand. Its actual
right shift represents division by two exactly, with no overflow. The already
proved native power computation therefore uses precisely the stored base and
half order, and popping that one cell retains its true written result.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

noncomputable section

open Execution ClassicalRoutines ClassicalAlgorithms

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The real destination contains the original modular power of the actual stored half order. -/
lemma result_toNat (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N))) (store : Store ctx)
    (baseValue : ClassicalAlgorithms.Modular.Residue (modulusSpec source))
    (orderValue : Word (phaseBits N + 1))
    (baseRead : store.read base = .canonicalResidue baseValue.toWord)
    (orderRead : store.read order = .unsignedWord orderValue) :
    (((step (model := model) source base order output store).1).read
      (.storage output.toCStorageRef)).toNat =
      baseValue.val ^ (orderValue.val / 2) % N := by
  let entered := store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh
  let shifted := entered.applyOp (shiftOp order)
  let halfValue : Word (phaseBits N + 1) :=
    ⟨orderValue.val / 2, (Nat.div_le_self _ _).trans_lt orderValue.isLt⟩
  let sourcePower : ClassicalAlgorithms.Modular.Pow.Input
      (modulusSpec source) (phaseBits N + 1) := ⟨baseValue, halfValue⟩
  have baseKeys : (liftInput (N := N) base).storageKeys = base.storageKeys :=
    CInputRef.storageKeys_underWorkspace base ctx.canonicalFreshKey
      (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
  have baseSeparate : (shiftOp order).outputRef.key ∉
      (liftInput (N := N) base).storageKeys := by
    change ctx.canonicalFreshKey ∉ (liftInput (N := N) base).storageKeys
    rw [baseKeys]
    exact fun present => ctx.canonicalFreshKey_fresh
      (CInputRef.storageKeys_subset_context base present)
  have shiftedBase : shifted.read (liftInput base) = .canonicalResidue baseValue.toWord :=
    (Store.read_applyOp_of_not_mem_storageKeys entered (shiftOp order)
      (liftInput base) baseSeparate).trans
      ((Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
        (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh base).trans baseRead)
  have originalOrder : entered.read (liftInput order) = .unsignedWord orderValue :=
    (Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
      (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh order).trans orderRead
  have shiftedHalf : shifted.read (.storage (halfRef ctx N).toCStorageRef) =
      .unsignedWord halfValue := by
    refine (Store.read_applyOp_output entered (shiftOp order)).trans ?_
    change CShape.wordShiftRight (phaseBits N + 1) (entered.read (liftInput order)) = _
    rw [originalOrder]
    apply congrArg CShape.Value.unsignedWord
    apply Fin.ext
    change (orderValue.val / 2) % 2 ^ (phaseBits N + 1) = orderValue.val / 2
    exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt orderValue.isLt)
  have actual := Modular.NativePower.nativePower_into_toNat (model := model)
    (modulusSpec source)
    (liftInput base) (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)
    shifted sourcePower ⟨shiftedBase, shiftedHalf⟩
  have popped := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
    (Modular.NativePower.intoStep (model := model) (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) shifted).1
    (.storage output.toCStorageRef)
  exact (congrArg CShape.Value.toNat popped).trans actual

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower
