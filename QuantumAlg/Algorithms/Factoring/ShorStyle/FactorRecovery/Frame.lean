/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Frame
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Frame
import all QuantumAlg.Components.Classical.ConstantWord.Semantics
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Structural reads through the complete actual factor tail

Each real branch preserves a read outside its seven scratch destinations and
surviving output. This internal statement includes native order recovery,
modular powering and both priority GCD branches. The enclosing physical scope
discharges every scratch condition from its actual fresh keys.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat} {shape : CShape}

/-- Internal write supports of the actual complete recovery and factor-selection tail. -/
structure FrameFree (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) : Prop where
  base : cells.base.key ∉ other.storageKeys
  order : cells.order.key ∉ other.storageKeys
  expanded : cells.expanded.key ∉ other.storageKeys
  zero : cells.zero.key ∉ other.storageKeys
  active : cells.active.key ∉ other.storageKeys
  positive : cells.positive.key ∉ other.storageKeys
  halfPower : cells.halfPower.key ∉ other.storageKeys
  output : output.key ∉ other.storageKeys

private theorem reduce_read_other (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (reduceStep source cells output store).1.read other = store.read other :=
  (NativeHalfFactorScope.read_other (halfRead cells) output other free.output
    (NativeHalfPower.step source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower store).1).trans
    (NativeHalfPower.read_other source (.storage cells.base.toCStorageRef)
      (orderRead cells) cells.halfPower other free.halfPower store)

private theorem checkedArm_read_other (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other)
    (value : CShape.Value .bit) (store : Store ctx) :
    (checkedArmStep source cells output value store).1.read other = store.read other := by
  cases value with
  | bit value =>
      cases value
      · exact Store.read_applyOp_of_not_mem_storageKeys store
          (packOutputOp cells output) other free.output
      · exact reduce_read_other source cells output other free store

private theorem checked_read_other (source : Input N) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (checkedStep source cells output store).1.read other = store.read other :=
  (checkedArm_read_other source cells output other free
    ((guardStore cells store).read (activeRead cells)) (guardStore cells store)).trans
    (guard_read_other cells other free.zero free.active free.positive store)

private theorem dispatchArm_read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other)
    (value : CShape.Value .bit) (store : Store ctx) :
    (dispatchArmStep source parameter cells output value store).1.read other =
      store.read other := by
  cases value with
  | bit value =>
      cases value
      · exact checked_read_other source cells output other free store
      · exact Store.read_applyOp_of_not_mem_storageKeys store
          (packEarlyOp parameter output) other free.output

private theorem dispatch_read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (dispatchStep source parameter cells output store).1.read other = store.read other :=
  dispatchArm_read_other source parameter cells output other free
    (store.read (.first (.second parameter))) store

private theorem recovered_read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (recoveredStep source parameter phase cells output store).1.read other =
      store.read other := by
  let packed := store.applyOp (packBaseOp parameter cells)
  let recovered := OrderRecovery.Native.intoStep (recoverySpec source)
    (.storage cells.base.toCStorageRef) phase cells.order packed
  exact (dispatch_read_other source parameter cells output other free
    (recovered.1.applyOp (unpackOrderOp cells))).trans
    ((Store.read_applyOp_of_not_mem_storageKeys recovered.1
      (unpackOrderOp cells) other free.expanded).trans
      ((OrderRecovery.Native.nativeRecovery_into_read_other (recoverySpec source)
        (.storage cells.base.toCStorageRef) phase cells.order other free.order packed).trans
        (Store.read_applyOp_of_not_mem_storageKeys store
          (packBaseOp parameter cells) other free.base)))

private theorem even_read_other (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (evenStep cells output store).1.read other = store.read other := by
  let cleared := store.applyOp (clearActiveOp cells)
  let selected := cleared.applyOp (setActiveOp cells)
  exact (Store.read_applyOp_of_not_mem_storageKeys (twoStep cells selected).1
    (packOutputOp cells output) other free.output).trans
    ((ConstantWord.constantWord_fold_read_other cells.halfPower
      (List.ofFn (ConstantWord.constantBits (modulusBits N) 2)) other
      free.halfPower selected).trans
      ((Store.read_applyOp_of_not_mem_storageKeys cleared (setActiveOp cells)
        other free.active).trans
        (Store.read_applyOp_of_not_mem_storageKeys store (clearActiveOp cells)
          other free.active)))

/-- Every actual modulus and stored-data branch preserves the complete original read frame. -/
theorem read_other (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N)
    (output : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (other : CInputRef ctx shape) (free : FrameFree cells output other) (store : Store ctx) :
    (step source parameter phase cells output store).1.read other = store.read other := by
  by_cases exceptional : 2 < N ∧ Even N
  · exact (congrArg (fun final : Store ctx => final.read other)
      (step_even_store source parameter phase cells output store exceptional)).trans
      (even_read_other cells output other free store)
  · exact (congrArg (fun final : Store ctx => final.read other)
      (step_recovered_store source parameter phase cells output store exceptional)).trans
      (recovered_read_other source parameter phase cells output other free store)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
