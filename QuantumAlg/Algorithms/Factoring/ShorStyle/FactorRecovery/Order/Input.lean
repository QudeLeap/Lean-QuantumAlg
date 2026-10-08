/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Encoding
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Parameters
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Correctness
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Frame

/-!
# The real recovered optional order and surviving sampler parameter

The actual prefix packs its stored base, runs intrinsic native order recovery
on the same stored phase bits, then unpacks the real optional result. Exact
read-support proofs preserve the original parameter and the canonical base.
The semantic input only identifies those existing source values; no recovery
certificate or independently supplied result enters the circuit.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail

open Execution ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {N : Nat}

omit [BitWord.Selected model] in
private theorem canonical_eq_of_val {width : Nat}
    (actual : CShape.Value (.canonicalResidue width)) (expected : Fin (2 ^ width))
    (same : actual.residueEncoding.val = expected.val) : actual = .canonicalResidue expected := by
  cases actual with
  | canonicalResidue value => exact congrArg CShape.Value.canonicalResidue (Fin.ext same)

/-- The exact actual prefix store just before the real sampler-priority dispatch. -/
def recoveredInputStore (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N) (store : Store ctx) :
    Store ctx :=
  (OrderRecovery.Native.intoStep (model := model) (recoverySpec source) (.storage
    cells.base.toCStorageRef)
    phase cells.order (store.applyOp (packBaseOp parameter cells))).1.applyOp (unpackOrderOp cells)

omit [BitWord.Selected model] in
/-- Base packing writes exactly the source input's canonical word from its original raw value. -/
theorem packedBase_source (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N))) (cells : Cells ctx N)
    (store : Store ctx)
    (baseValue : (store.read parameter).first.toNat = semantic.base.val) :
    (store.applyOp (packBaseOp parameter cells)).read (.storage cells.base.toCStorageRef) =
      .canonicalResidue semantic.base :=
  canonical_eq_of_val _ _ ((packBase_result parameter cells store).trans baseValue)

/-- The real optional order from intrinsic recovery supplies the actual decoded tag and word. -/
theorem recoveredInput_order (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N) (store : Store ctx)
    (baseFree : cells.base.key ∉ phase.storageKeys)
    (baseValue : (store.read parameter).first.toNat = semantic.base.val)
    (phaseValue : store.read phase = .bits semantic.terminalBits) :
    (recoveredInputStore (model := model) source parameter phase cells store).read (expandedRead
      cells) =
      match ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
          (recoverySpec source) semantic with
      | none => .product (.bit false) (CShape.wordOfNat (phaseBits N + 1) 0)
      | some word => .product (.bit true) (.unsignedWord word) := by
  let packed := store.applyOp (packBaseOp parameter cells)
  have packedPhase : packed.read phase = .bits semantic.terminalBits :=
    (Store.read_applyOp_of_not_mem_storageKeys store (packBaseOp parameter cells) phase
      baseFree).trans phaseValue
  have actual := OrderRecovery.Native.nativeRecovery_into_result (model := model) (recoverySpec
    source) semantic
    (.storage cells.base.toCStorageRef) phase cells.order packed
    (packedBase_source source semantic parameter cells store baseValue) packedPhase
  change (OrderRecovery.Native.intoStep (model := model) (recoverySpec source)
    (.storage cells.base.toCStorageRef) phase cells.order packed).1.read
      (.storage cells.order.toCStorageRef) =
        OrderRecovery.Native.encodeOutput
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (recoverySpec source) semantic) at actual
  cases recovered : ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
      (recoverySpec source) semantic with
  | none =>
    exact unpackOrder_encoded cells
      (OrderRecovery.Native.intoStep (model := model) (recoverySpec source) (.storage
        cells.base.toCStorageRef)
        phase cells.order packed).1 none (by simpa only [recovered] using actual)
  | some word =>
    exact unpackOrder_encoded cells
      (OrderRecovery.Native.intoStep (model := model) (recoverySpec source) (.storage
        cells.base.toCStorageRef)
        phase cells.order packed).1 (some word) (by simpa only [recovered] using actual)

/-- The actual recovery prefix keeps the same retained sampler parameter for its priority branch. -/
theorem recoveredInput_parameter (source : Input N)
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N) (store : Store ctx)
    (baseFree : cells.base.key ∉ parameter.storageKeys)
    (orderFree : cells.order.key ∉ parameter.storageKeys)
    (expandedFree : cells.expanded.key ∉ parameter.storageKeys) :
    (recoveredInputStore (model := model) source parameter phase cells store).read parameter =
      store.read parameter :=
  (Store.read_applyOp_of_not_mem_storageKeys
    (OrderRecovery.Native.intoStep (model := model) (recoverySpec source) (.storage
      cells.base.toCStorageRef)
      phase cells.order (store.applyOp (packBaseOp parameter cells))).1
    (unpackOrderOp cells) parameter expandedFree).trans
    ((OrderRecovery.Native.nativeRecovery_into_read_other (model := model) (recoverySpec source)
      (.storage cells.base.toCStorageRef) phase cells.order parameter orderFree
      (store.applyOp (packBaseOp parameter cells))).trans
      (Store.read_applyOp_of_not_mem_storageKeys store (packBaseOp parameter cells)
        parameter baseFree))

/-- The same real canonical base remains available to the subsequent actual half-order power. -/
theorem recoveredInput_base (source : Input N)
    (semantic : ClassicalAlgorithms.OrderRecovery.Input (recoverySpec source))
    (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (phase : CInputRef ctx (.bits (phaseBits N))) (cells : Cells ctx N) (store : Store ctx)
    (orderBase : cells.order.key ≠ cells.base.key)
    (expandedBase : cells.expanded.key ≠ cells.base.key)
    (baseValue : (store.read parameter).first.toNat = semantic.base.val) :
    (recoveredInputStore (model := model) source parameter phase cells store).read
      (.storage cells.base.toCStorageRef) = .canonicalResidue semantic.base :=
  (Store.read_applyOp_of_not_mem_storageKeys
    (OrderRecovery.Native.intoStep (model := model) (recoverySpec source) (.storage
      cells.base.toCStorageRef)
      phase cells.order (store.applyOp (packBaseOp parameter cells))).1
    (unpackOrderOp cells) (.storage cells.base.toCStorageRef)
    (fun member => expandedBase (List.mem_singleton.mp member))).trans
    ((OrderRecovery.Native.nativeRecovery_into_read_other (model := model) (recoverySpec source)
      (.storage cells.base.toCStorageRef) phase cells.order (.storage cells.base.toCStorageRef)
      (fun member => orderBase (List.mem_singleton.mp member))
      (store.applyOp (packBaseOp parameter cells))).trans
      (packedBase_source source semantic parameter cells store baseValue))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.FactorRecovery.NativeFactorTail
