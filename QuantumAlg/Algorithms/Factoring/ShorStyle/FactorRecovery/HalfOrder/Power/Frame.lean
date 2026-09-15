/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Execution
import all QuantumAlg.Components.Classical.Modular.NativePower.Preservation
import all QuantumAlg.Core.Execution.Store.Read

/-!
# The actual half-order power preserves the rest of its original classical frame

The real half-order head is fresh. The existing modular-power frame law keeps
every original structural operand outside the declared result, through its
own nested workspace as well as the surrounding actual shift and release.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Only the actual result can change among the pre-existing structural reads. -/
theorem read_other (source : Input N)
    (base : CInputRef ctx (.canonicalResidue (modulusBits N)))
    (order : CInputRef ctx (.unsignedWord (phaseBits N + 1)))
    (output : CWriteRef ctx (.unsignedWord (modulusBits N)))
    {shape : CShape} (other : CInputRef ctx shape)
    (separate : output.key ∉ other.storageKeys) (store : Store ctx) :
    (step source base order output store).1.read other = store.read other := by
  let entered := store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord (phaseBits N + 1))
    ctx.canonicalFreshKey_fresh
  let shifted := entered.applyOp (shiftOp order)
  have otherKeys : (liftInput (N := N) other).storageKeys = other.storageKeys :=
    CInputRef.storageKeys_underWorkspace other ctx.canonicalFreshKey
      (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
  have halfFree : (shiftOp order).outputRef.key ∉ (liftInput (N := N) other).storageKeys := by
    change ctx.canonicalFreshKey ∉ (liftInput (N := N) other).storageKeys
    rw [otherKeys]
    exact fun member => ctx.canonicalFreshKey_fresh
      (CInputRef.storageKeys_subset_context other member)
  have outputFree : (liftWrite (N := N) output).key ∉
      (liftInput (N := N) other).storageKeys := by
    rw [otherKeys]
    exact separate
  have powerSame := Modular.NativePower.nativePower_into_read_other (modulusSpec source)
    (liftInput base) (.storage (halfRef ctx N).toCStorageRef) (liftWrite output)
    shifted (liftInput other) outputFree
  have shiftedSame := Store.read_applyOp_of_not_mem_storageKeys entered (shiftOp order)
    (liftInput other) halfFree
  have enteredSame := Store.read_pushWorkspace_underWorkspace store ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh other
  have exited := Store.read_popWorkspace_underWorkspace ctx.canonicalFreshKey
    (.unsignedWord (phaseBits N + 1)) ctx.canonicalFreshKey_fresh
    (Modular.NativePower.intoStep (modulusSpec source) (liftInput base)
      (.storage (halfRef ctx N).toCStorageRef) (liftWrite output) shifted).1 other
  exact exited.trans (powerSame.trans (shiftedSame.trans enteredSame))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeHalfPower
